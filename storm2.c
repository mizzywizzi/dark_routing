#define SDL_MAIN_HANDLED
#include <SDL2/SDL.h>
#include <SDL2/SDL_image.h>
#include <SDL2/SDL_mixer.h>
#include <SDL2/SDL_ttf.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

int winWidth = 1920;
int winHeight = 1080;
#define TOPBAR 0
#define GRID_SCALE 4
#define PADDING_COST 50.0f
#define STORM_THRESHOLD 30.0f
#define VELOCITY_SAMPLES 5

// --- Map Boundary Constants (User Provided) ---
#define MAP_NORTH 85.14f
#define MAP_SOUTH -31.78f
#define MAP_WEST -16.08f
#define MAP_EAST 179.33f

typedef struct {
  float x, y;
  int valid;
  float alpha;
} Point;
typedef struct {
  int r, c;
} GridPos;
typedef struct Node {
  GridPos pos;
  float g, h, f;
  struct Node *parent;
} Node;

typedef struct {
  Node **nodes;
  int size;
} MinHeap;

// --- A* Heap Functions ---
void pushHeap(MinHeap *heap, Node *node) {
  int i = heap->size++;
  while (i > 0) {
    int p = (i - 1) / 2;
    if (heap->nodes[p]->f <= node->f)
      break;
    heap->nodes[i] = heap->nodes[p];
    i = p;
  }
  heap->nodes[i] = node;
}

Node *popHeap(MinHeap *heap) {
  if (heap->size == 0)
    return NULL;
  Node *res = heap->nodes[0];
  Node *last = heap->nodes[--heap->size];
  int i = 0;
  while (i * 2 + 1 < heap->size) {
    int child = i * 2 + 1;
    if (child + 1 < heap->size &&
        heap->nodes[child + 1]->f < heap->nodes[child]->f)
      child++;
    if (last->f <= heap->nodes[child]->f)
      break;
    heap->nodes[i] = heap->nodes[child];
    i = child;
  }
  heap->nodes[i] = last;
  return res;
}

// --- Globals ---
float zoom = 1.0f, targetZoom = 1.0f;
float camX = 0, camY = 0;
float velX = 0.0f, velY = 0.0f;
float friction = 0.94f;
float frameVelX[VELOCITY_SAMPLES] = {0};
float frameVelY[VELOCITY_SAMPLES] = {0};
int velIdx = 0;
float zoomWorldX = 0, zoomWorldY = 0; // World position to zoom towards
int zoomMouseX = 0, zoomMouseY = 0;   // Screen position of mouse during zoom

Point p1 = {0, 0, 0, 0}, p2 = {0, 0, 0, 0};
SDL_Texture *mapTex = NULL, *startTex = NULL, *endTex = NULL;
Mix_Chunk *tickSound = NULL;
int mapWidth, mapHeight;
char infoText[128] = "Click to set A and B";
char shipName[64] = "Unknown", shipSpeed[32] = "0 kts", shipMode[32] = "N/A";
float shipSpeedKnots = 14.0f;
float routeDistance = 0.0f; // Total distance in km
float routeETA = 0.0f;      // Estimated time in days
float routeFuel = 0.0f;     // Fuel estimate in tons
float routeRisk = 0.0f;     // Max risk percentage (0-100)
char routeStatus[32] = "PENDING";

void loadShipInfo() {
  FILE *f = fopen("ship_info.txt", "r");
  if (f) {
    char line[256];
    if (fgets(line, sizeof(line), f)) {
      char *sptr = strstr(line, " speed=");
      char *mptr = strstr(line, " mode=");
      if (sptr && mptr) {
        *sptr = '\0';
        *mptr = '\0';
        strncpy(shipName, line, sizeof(shipName) - 1);
        strncpy(shipSpeed, sptr + 7, sizeof(shipSpeed) - 1);
        strncpy(shipMode, mptr + 6, sizeof(shipMode) - 1);
        // Clean newlines
        char *n = strchr(shipMode, '\n');
        if (n)
          *n = '\0';
        n = strchr(shipMode, '\r');
        if (n)
          *n = '\0';
        // Parse numeric speed
        shipSpeedKnots = atof(sptr + 7);
      }
    }
    fclose(f);
  }
}

unsigned char *collisionGrid = NULL;
float *weatherGrid = NULL;
int gridW, gridH;
GridPos *finalPath = NULL;
int pathLen = 0;

// --- Coordinate Helpers (Mapped to User Bounding Box) ---
int worldToScreenX(float wx) {
  return (int)((wx - camX) * zoom + winWidth / 2);
}
int worldToScreenY(float wy) {
  return (int)((wy - camY) * zoom + winHeight / 2 + TOPBAR);
}
float screenToWorldX(int sx) { return (sx - winWidth / 2) / zoom + camX; }
float screenToWorldY(int sy) {
  return (sy - TOPBAR - winHeight / 2) / zoom + camY;
}
float worldToPixelX(float wx) { return wx + mapWidth / 2.0f; }
float worldToPixelY(float wy) { return wy + mapHeight / 2.0f; }

float pixelToLat(float pixel_y) {
  // Derived from data points: m = -1296.0, c = 3988.0
  return (2.0f * atanf(expf((pixel_y - 3988.0f) / -1296.0f)) -
          (float)M_PI / 2.0f) *
         180.0f / (float)M_PI;
}

float pixelToLon(float pixel_x) {
  // Derived from data points: scale = 22.7835, c = 3870.0
  return (pixel_x - 3870.0f) / 22.7835f;
}

void formatCoord(char *buf, size_t size, float lat, float lon) {
  char latDir = lat >= 0 ? 'N' : 'S';
  char lonDir = lon >= 0 ? 'E' : 'W';
  snprintf(buf, size, "%.2f %c %.2f %c", fabsf(lat), latDir, fabsf(lon),
           lonDir);
}

void wrapCamera() {
  float half = mapWidth * 0.5f;
  if (camX > half)
    camX -= mapWidth;
  else if (camX < -half)
    camX += mapWidth;
}

void drawRoundedRect(SDL_Renderer *ren, SDL_Rect rect, int radius,
                     SDL_Color color, int glossy) {
  // Draw filled rounded rectangle
  SDL_SetRenderDrawColor(ren, color.r, color.g, color.b, color.a);

  // Main body rectangles
  SDL_Rect top = {rect.x + radius, rect.y, rect.w - 2 * radius, radius};
  SDL_Rect middle = {rect.x, rect.y + radius, rect.w, rect.h - 2 * radius};
  SDL_Rect bottom = {rect.x + radius, rect.y + rect.h - radius,
                     rect.w - 2 * radius, radius};

  SDL_RenderFillRect(ren, &top);
  SDL_RenderFillRect(ren, &middle);
  SDL_RenderFillRect(ren, &bottom);

  // Draw corners using circles (approximated with filled rects)
  for (int w = 0; w < radius * 2; w++) {
    for (int h = 0; h < radius * 2; h++) {
      int dx = radius - w;
      int dy = radius - h;
      if (dx * dx + dy * dy <= radius * radius) {
        SDL_RenderDrawPoint(ren, rect.x + w, rect.y + h); // Top-left
        SDL_RenderDrawPoint(ren, rect.x + rect.w - w - 1,
                            rect.y + h); // Top-right
        SDL_RenderDrawPoint(ren, rect.x + w,
                            rect.y + rect.h - h - 1); // Bottom-left
        SDL_RenderDrawPoint(ren, rect.x + rect.w - w - 1,
                            rect.y + rect.h - h - 1); // Bottom-right
      }
    }
  }

  // Add glossy effect (gradient overlay at top) - smooth at corners
  if (glossy) {
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    int glossHeight = rect.h / 3;
    for (int i = 0; i < glossHeight; i++) {
      int alpha = (int)(40.0f * (1.0f - (float)i / glossHeight));
      SDL_SetRenderDrawColor(ren, 255, 255, 255, alpha);

      // Calculate line width based on distance from top (avoid sharp corners)
      int lineY = rect.y + radius + i;
      int startX = rect.x + radius;
      int endX = rect.x + rect.w - radius;

      // If we're in the rounded corner area, adjust the line width
      if (i < radius) {
        int cornerOffset =
            (int)sqrtf(radius * radius - (radius - i) * (radius - i));
        startX = rect.x + radius - cornerOffset;
        endX = rect.x + rect.w - radius + cornerOffset;
      }

      SDL_RenderDrawLine(ren, startX, lineY, endX, lineY);
    }
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_NONE);
  }
}

void drawRoundedRectBorder(SDL_Renderer *ren, SDL_Rect rect, int radius,
                           SDL_Color color) {
  SDL_SetRenderDrawColor(ren, color.r, color.g, color.b, color.a);

  // Draw straight edges
  SDL_RenderDrawLine(ren, rect.x + radius, rect.y, rect.x + rect.w - radius - 1,
                     rect.y); // Top
  SDL_RenderDrawLine(ren, rect.x + radius, rect.y + rect.h - 1,
                     rect.x + rect.w - radius - 1,
                     rect.y + rect.h - 1); // Bottom
  SDL_RenderDrawLine(ren, rect.x, rect.y + radius, rect.x,
                     rect.y + rect.h - radius - 1); // Left
  SDL_RenderDrawLine(ren, rect.x + rect.w - 1, rect.y + radius,
                     rect.x + rect.w - 1,
                     rect.y + rect.h - radius - 1); // Right

  // Draw rounded corners - only the arc portions
  for (int w = 0; w < radius * 2; w++) {
    for (int h = 0; h < radius * 2; h++) {
      int dx = radius - w;
      int dy = radius - h;
      int dist = dx * dx + dy * dy;
      // Draw only the border pixels (at radius distance)
      if (dist <= radius * radius && dist > (radius - 1) * (radius - 1)) {
        // Top-left corner (only draw if in top-left quadrant)
        if (w <= radius && h <= radius) {
          SDL_RenderDrawPoint(ren, rect.x + w, rect.y + h);
        }
        // Top-right corner (only draw if in top-right quadrant)
        if (w >= radius && h <= radius) {
          SDL_RenderDrawPoint(ren, rect.x + rect.w - (radius * 2 - w),
                              rect.y + h);
        }
        // Bottom-left corner (only draw if in bottom-left quadrant)
        if (w <= radius && h >= radius) {
          SDL_RenderDrawPoint(ren, rect.x + w,
                              rect.y + rect.h - (radius * 2 - h));
        }
        // Bottom-right corner (only draw if in bottom-right quadrant)
        if (w >= radius && h >= radius) {
          SDL_RenderDrawPoint(ren, rect.x + rect.w - (radius * 2 - w),
                              rect.y + rect.h - (radius * 2 - h));
        }
      }
    }
  }
}

// --- Weather Implementation ---
void updateWeatherSimulation() {
  if (!weatherGrid)
    return;
  for (int r = 0; r < gridH; r++) {
    for (int c = 0; c < gridW; c++) {
      float lat = pixelToLat(r * GRID_SCALE);
      float lon = pixelToLon(c * GRID_SCALE);

      // Simulating a storm near the center of the Mediterranean/Atlantic
      // Center: 35.0 Lat, 15.0 Lon. Radius: 10 degrees
      float dist = sqrtf(pow(lat - 35.0f, 2) + pow(lon - 15.0f, 2));
      if (dist < 10.0f)
        weatherGrid[r * gridW + c] = 55.0f; // High wind speed
      else
        weatherGrid[r * gridW + c] = 5.0f;
    }
  }
}

// --- Logic ---
void createCollisionGrid(SDL_Surface *surf) {
  gridW = surf->w / GRID_SCALE;
  gridH = surf->h / GRID_SCALE;
  collisionGrid = (unsigned char *)malloc(gridW * gridH);
  weatherGrid = (float *)calloc(gridW * gridH, sizeof(float));

  Uint32 *pixels = (Uint32 *)surf->pixels;
  for (int y = 0; y < gridH; y++) {
    for (int x = 0; x < gridW; x++) {
      Uint32 pixel = pixels[(y * GRID_SCALE * surf->w) + (x * GRID_SCALE)];
      Uint8 r, g, b;
      SDL_GetRGB(pixel, surf->format, &r, &g, &b);
      collisionGrid[y * gridW + x] = (r == 38 && g == 38 && b == 38) ? 0 : 1;
    }
  }
  for (int y = 1; y < gridH - 1; y++) {
    for (int x = 1; x < gridW - 1; x++) {
      if (collisionGrid[y * gridW + x] == 0) {
        for (int dy = -1; dy <= 1; dy++) {
          for (int dx = -1; dx <= 1; dx++) {
            if (collisionGrid[(y + dy) * gridW + (x + dx)] == 1) {
              collisionGrid[y * gridW + x] = 2;
              break;
            }
          }
        }
      }
    }
  }
  updateWeatherSimulation();
}

void snapToWater(Point *p) {
  int c = (int)(p->x + mapWidth / 2) / GRID_SCALE;
  int r = (int)(p->y + mapHeight / 2) / GRID_SCALE;
  if (r >= 0 && r < gridH && c >= 0 && c < gridW &&
      collisionGrid[r * gridW + c] != 1)
    return;
  for (int radius = 1; radius < 25; radius++) {
    for (int dr = -radius; dr <= radius; dr++) {
      for (int dc = -radius; dc <= radius; dc++) {
        int nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW &&
            collisionGrid[nr * gridW + nc] != 1) {
          p->x = (nc * GRID_SCALE) - mapWidth / 2.0f + (GRID_SCALE / 2.0f);
          p->y = (nr * GRID_SCALE) - mapHeight / 2.0f + (GRID_SCALE / 2.0f);
          return;
        }
      }
    }
  }
}

void calculateRouteStats() {
  if (!finalPath || pathLen == 0) {
    routeDistance = 0.0f;
    routeETA = 0.0f;
    routeFuel = 0.0f;
    routeRisk = 0.0f;
    strcpy(routeStatus, "PENDING");
    return;
  }

  // Calculate total distance in km
  routeDistance = 0.0f;
  float maxRisk = 0.0f;

  for (int i = 0; i < pathLen - 1; i++) {
    float wx1 = finalPath[i].c * GRID_SCALE - mapWidth / 2.0f;
    float wy1 = finalPath[i].r * GRID_SCALE - mapHeight / 2.0f;
    float wx2 = finalPath[i + 1].c * GRID_SCALE - mapWidth / 2.0f;
    float wy2 = finalPath[i + 1].r * GRID_SCALE - mapHeight / 2.0f;

    // Convert to lat/lon for accurate distance
    float lat1 = pixelToLat(worldToPixelY(wy1));
    float lon1 = pixelToLon(worldToPixelX(wx1));
    float lat2 = pixelToLat(worldToPixelY(wy2));
    float lon2 = pixelToLon(worldToPixelX(wx2));

    // Haversine formula for distance
    float dLat = (lat2 - lat1) * M_PI / 180.0f;
    float dLon = (lon2 - lon1) * M_PI / 180.0f;
    float a = sinf(dLat / 2) * sinf(dLat / 2) +
              cosf(lat1 * M_PI / 180.0f) * cosf(lat2 * M_PI / 180.0f) *
                  sinf(dLon / 2) * sinf(dLon / 2);
    float c = 2 * atan2f(sqrtf(a), sqrtf(1 - a));
    routeDistance += 6371.0f * c; // Earth radius in km

    // Track max risk along route
    float wind = weatherGrid[finalPath[i].r * gridW + finalPath[i].c];
    if (wind > STORM_THRESHOLD) {
      float risk = (wind / 100.0f) * 100.0f;
      if (risk > maxRisk)
        maxRisk = risk;
    }
  }

  // Calculate ETA in days (distance / speed, convert knots to km/day)
  float speedKmPerDay = shipSpeedKnots * 1.852f * 24.0f; // knots to km/day
  routeETA = routeDistance / speedKmPerDay;

  // Estimate fuel consumption (rough estimate: ~0.5 tons per 100km for cargo
  // ship)
  routeFuel = routeDistance * 0.5f / 100.0f;

  // Risk percentage
  routeRisk = maxRisk;
  if (routeRisk > 100.0f)
    routeRisk = 100.0f;

  strcpy(routeStatus, "OPTIMIZED");
}

void astar() {
  if (!p1.valid || !p2.valid)
    return;
  snapToWater(&p1);
  snapToWater(&p2);
  int startC = (int)(p1.x + mapWidth / 2) / GRID_SCALE;
  int startR = (int)(p1.y + mapHeight / 2) / GRID_SCALE;
  int endC = (int)(p2.x + mapWidth / 2) / GRID_SCALE;
  int endR = (int)(p2.y + mapHeight / 2) / GRID_SCALE;

  MinHeap openList = {malloc(sizeof(Node *) * gridW * gridH), 0};
  Node *nodes = (Node *)calloc(gridW * gridH, sizeof(Node));
  float *gScore = (float *)malloc(gridW * gridH * sizeof(float));
  for (int i = 0; i < gridW * gridH; i++)
    gScore[i] = 1e9f;

  int startIdx = startR * gridW + startC;
  gScore[startIdx] = 0;
  nodes[startIdx].pos = (GridPos){startR, startC};
  nodes[startIdx].f = sqrtf(pow(startR - endR, 2) + pow(startC - endC, 2));
  pushHeap(&openList, &nodes[startIdx]);

  int found = 0;
  while (openList.size > 0) {
    Node *curr = popHeap(&openList);
    if (curr->pos.r == endR && curr->pos.c == endC) {
      found = 1;
      pathLen = 0;
      Node *temp = curr;
      while (temp) {
        pathLen++;
        temp = temp->parent;
      }
      if (finalPath)
        free(finalPath);
      finalPath = malloc(sizeof(GridPos) * pathLen);
      temp = curr;
      for (int i = pathLen - 1; i >= 0; i--) {
        finalPath[i] = temp->pos;
        temp = temp->parent;
      }
      break;
    }

    for (int dr = -1; dr <= 1; dr++) {
      for (int dc = -1; dc <= 1; dc++) {
        if (dr == 0 && dc == 0)
          continue;
        int nr = curr->pos.r + dr, nc = curr->pos.c + dc;
        if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW ||
            collisionGrid[nr * gridW + nc] == 1)
          continue;

        float stepCost = (dr == 0 || dc == 0) ? 1.0f : 1.414f;
        if (collisionGrid[nr * gridW + nc] == 2)
          stepCost += PADDING_COST;

        // --- WEATHER PENALTY ---
        float wind = weatherGrid[nr * gridW + nc];
        if (wind > STORM_THRESHOLD) {
          stepCost +=
              (wind * 8.0f); // Penalize storms to force routing around them
        }

        float tentativeG = gScore[curr->pos.r * gridW + curr->pos.c] + stepCost;
        if (tentativeG < gScore[nr * gridW + nc]) {
          int idx = nr * gridW + nc;
          gScore[idx] = tentativeG;
          nodes[idx].pos = (GridPos){nr, nc};
          nodes[idx].parent = curr;
          nodes[idx].g = tentativeG;
          nodes[idx].h = sqrtf(pow(nr - endR, 2) + pow(nc - endC, 2)) * 1.2f;
          nodes[idx].f = nodes[idx].g + nodes[idx].h;
          pushHeap(&openList, &nodes[idx]);
        }
      }
    }
  }
  free(openList.nodes);
  free(nodes);
  free(gScore);
  snprintf(infoText, sizeof(infoText),
           found ? "Route Calculated (Storms Avoided)" : "No Route Possible");
  calculateRouteStats();
}

int main(int argc, char *argv[]) {
  SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO);

  SDL_DisplayMode dm;
  if (SDL_GetCurrentDisplayMode(0, &dm) == 0) {
    winWidth = (int)(dm.w * 0.9f);
    winHeight = (int)(dm.h * 0.9f);
  }
  TTF_Init();
  IMG_Init(IMG_INIT_PNG);
  Mix_OpenAudio(22050, MIX_DEFAULT_FORMAT, 2, 512);

  SDL_Window *win =
      SDL_CreateWindow("Sea Route Planner - Storm Avoidance",
                       SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED, winWidth,
                       winHeight + TOPBAR, SDL_WINDOW_RESIZABLE);
  SDL_Renderer *ren = SDL_CreateRenderer(
      win, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);

  tickSound = Mix_LoadWAV("assets/tick.wav");
  startTex = IMG_LoadTexture(ren, "assets/start.png");
  endTex = IMG_LoadTexture(ren, "assets/end.png");
  loadShipInfo();
  SDL_Surface *tempSurf = IMG_Load("assets/temp1.png");
  SDL_Surface *surf =
      SDL_ConvertSurfaceFormat(tempSurf, SDL_PIXELFORMAT_ARGB8888, 0);
  SDL_FreeSurface(tempSurf);
  mapWidth = surf->w;
  mapHeight = surf->h;
  createCollisionGrid(surf);
  mapTex = SDL_CreateTextureFromSurface(ren, surf);
  SDL_FreeSurface(surf);

  // Initial camera centering at pixel (5600, 3400)
  camX = 5600.0f - mapWidth / 2.0f;
  camY = 3400.0f - mapHeight / 2.0f;

  TTF_Font *font = TTF_OpenFont("assets/fonts/DejaVuSans.ttf", 16);
  TTF_Font *smallFont = TTF_OpenFont("assets/fonts/DejaVuSans.ttf", 12);
  TTF_Font *valueFont = TTF_OpenFont("assets/fonts/JetBrainsMono-ExtraBold.ttf",
                                     18); // For numbers/values
  TTF_Font *labelFont =
      TTF_OpenFont("assets/fonts/Inter_18pt-Regular.ttf", 14); // For labels
  TTF_Font *titleFont =
      TTF_OpenFont("assets/fonts/Inter_18pt-Regular.ttf", 16); // For title

  if (!font || !smallFont || !valueFont || !labelFont || !titleFont) {
    printf("Font error: %s\n", TTF_GetError());
  }

  int dragging = 0, lastMouseX = 0, lastMouseY = 0, running = 1;
  Uint32 lastTicks = SDL_GetTicks();
  Uint32 lastZoomSound = 0;

  while (running) {
    Uint32 currentTicks = SDL_GetTicks();
    float deltaTime = (currentTicks - lastTicks) / 1000.0f;
    if (deltaTime > 0.1f)
      deltaTime = 0.016f;
    lastTicks = currentTicks;

    SDL_Event e;
    while (SDL_PollEvent(&e)) {
      if (e.type == SDL_QUIT)
        running = 0;
      if (e.type == SDL_WINDOWEVENT &&
          e.window.event == SDL_WINDOWEVENT_RESIZED) {
        winWidth = e.window.data1;
        winHeight = e.window.data2;
      }
      if (e.type == SDL_MOUSEWHEEL) {
        int mx, my;
        SDL_GetMouseState(&mx, &my);

        // Store the world position under the mouse and the mouse screen
        // position
        zoomWorldX = screenToWorldX(mx);
        zoomWorldY = screenToWorldY(my);
        zoomMouseX = mx;
        zoomMouseY = my;

        targetZoom += e.wheel.y * 0.12f;
        if (targetZoom < 0.289f)
          targetZoom = 0.289f;
        if (targetZoom > 2.0f)
          targetZoom = 2.0f; // Limit zoom out
        if (tickSound && (currentTicks - lastZoomSound > 100)) {
          Mix_PlayChannel(-1, tickSound, 0);
          lastZoomSound = currentTicks;
        }
      }
      if (e.type == SDL_MOUSEBUTTONDOWN && e.button.button == SDL_BUTTON_LEFT) {
        // Logic: 1st click -> A, 2nd click -> B, 3rd click -> Clear & Set A
        float wx = screenToWorldX(e.button.x), wy = screenToWorldY(e.button.y);
        if (p1.valid && p2.valid) {
          // Reset state on 3rd click
          p1.valid = 0;
          p2.valid = 0;
          pathLen = 0;
          if (finalPath) {
            free(finalPath);
            finalPath = NULL;
          }
          p1 = (Point){wx, wy, 1, 0}; // Set new A
        } else if (!p1.valid) {
          p1 = (Point){wx, wy, 1, 0};
        } else if (!p2.valid) {
          p2 = (Point){wx, wy, 1, 0};
          astar(); // Auto-compute path
        }
      }
      if (e.type == SDL_MOUSEBUTTONDOWN &&
          e.button.button == SDL_BUTTON_RIGHT) {
        dragging = 1;
        lastMouseX = e.button.x;
        lastMouseY = e.button.y;
        velX = velY = 0;
        for (int i = 0; i < VELOCITY_SAMPLES; i++) {
          frameVelX[i] = 0;
          frameVelY[i] = 0;
        }
      }
      if (e.type == SDL_MOUSEBUTTONUP && e.button.button == SDL_BUTTON_RIGHT) {
        dragging = 0;
        float avgX = 0, avgY = 0;
        for (int i = 0; i < VELOCITY_SAMPLES; i++) {
          avgX += frameVelX[i];
          avgY += frameVelY[i];
        }
        velX = avgX / VELOCITY_SAMPLES;
        velY = avgY / VELOCITY_SAMPLES;
      }
      if (e.type == SDL_MOUSEMOTION && dragging) {
        float dx = (e.motion.x - lastMouseX) / zoom;
        float dy = (e.motion.y - lastMouseY) / zoom;
        camX -= dx;
        camY -= dy;
        frameVelX[velIdx] = -dx / deltaTime;
        frameVelY[velIdx] = -dy / deltaTime;
        velIdx = (velIdx + 1) % VELOCITY_SAMPLES;
        lastMouseX = e.motion.x;
        lastMouseY = e.motion.y;
        wrapCamera();
      }
    }

    // Smooth zoom interpolation with camera adjustment to keep world point
    // under mouse
    float prevZoom = zoom;
    zoom += (targetZoom - zoom) * 0.12f;

    // Adjust camera to keep zoomWorldX, zoomWorldY under the mouse cursor
    if (fabs(targetZoom - zoom) > 0.001f) {
      camX = zoomWorldX - (zoomMouseX - winWidth / 2.0f) / zoom;
      camY = zoomWorldY - (zoomMouseY - winHeight / 2.0f - TOPBAR) / zoom;
      printf("Zoom: %.3f (Target: %.3f)\n", zoom, targetZoom);
    }

    if (!dragging) {
      camX += velX * deltaTime;
      camY += velY * deltaTime;
      velX *= friction;
      velY *= friction;
      if (fabs(velX) < 1.0f)
        velX = 0;
      if (fabs(velY) < 1.0f)
        velY = 0;
      wrapCamera();
    }

    // Vertical Panning Constraints
    float limit = (mapHeight / 2.0f) - (winHeight / 2.0f) / zoom;
    if (limit < 0)
      camY = 0;
    else {
      if (camY < -limit)
        camY = -limit;
      if (camY > limit)
        camY = limit;
    }

    if (p1.valid && p1.alpha < 255)
      p1.alpha += 15;
    if (p2.valid && p2.alpha < 255)
      p2.alpha += 15;

    // Rendering start: Get actual window size
    int currW, currH;
    SDL_GetRendererOutputSize(ren, &currW, &currH);

    SDL_SetRenderDrawColor(ren, 255, 255, 255, 255);
    SDL_RenderClear(ren);

    for (int dx = -1; dx <= 1; dx++) {
      SDL_Rect dst = {worldToScreenX(-mapWidth / 2 + dx * mapWidth),
                      worldToScreenY(-mapHeight / 2), (int)(mapWidth * zoom),
                      (int)(mapHeight * zoom)};
      SDL_RenderCopy(ren, mapTex, NULL, &dst);
    }

    // --- Render Weather Overlay ---
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    for (int r = 0; r < gridH; r += 2) {
      for (int c = 0; c < gridW; c += 2) {
        if (weatherGrid[r * gridW + c] > STORM_THRESHOLD) {
          SDL_SetRenderDrawColor(ren, 255, 0, 0, 50);
          float wx = c * GRID_SCALE - mapWidth / 2.0f;
          float wy = r * GRID_SCALE - mapHeight / 2.0f;
          SDL_Rect wr = {worldToScreenX(wx), worldToScreenY(wy),
                         (int)(GRID_SCALE * 2 * zoom),
                         (int)(GRID_SCALE * 2 * zoom)};
          SDL_RenderFillRect(ren, &wr);
        }
      }
    }

    if (finalPath) {
      // Draw path with thicker, more visible lines
      SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
      for (int i = 0; i < pathLen - 1; i++) {
        float wx1 = finalPath[i].c * GRID_SCALE - mapWidth / 2.0f,
              wy1 = finalPath[i].r * GRID_SCALE - mapHeight / 2.0f;
        float wx2 = finalPath[i + 1].c * GRID_SCALE - mapWidth / 2.0f,
              wy2 = finalPath[i + 1].r * GRID_SCALE - mapHeight / 2.0f;
        if (fabs(wx1 - wx2) < mapWidth / 2) {
          int sx1 = worldToScreenX(wx1), sy1 = worldToScreenY(wy1);
          int sx2 = worldToScreenX(wx2), sy2 = worldToScreenY(wy2);
          // Draw thicker line with multiple passes
          for (int offset = -2; offset <= 2; offset++) {
            SDL_SetRenderDrawColor(ren, 0, 180, 255, offset == 0 ? 255 : 100);
            SDL_RenderDrawLine(ren, sx1 + offset, sy1, sx2 + offset, sy2);
            SDL_RenderDrawLine(ren, sx1, sy1 + offset, sx2, sy2 + offset);
          }
        }
      }
    }

    Point *pts[2] = {&p1, &p2};
    const char *labels[2] = {"A", "B"};
    SDL_Texture *icons[2] = {startTex, endTex};
    for (int i = 0; i < 2; i++) {
      if (pts[i]->valid) {
        SDL_SetTextureAlphaMod(icons[i], (Uint8)pts[i]->alpha);
        SDL_Rect r = {worldToScreenX(pts[i]->x) - 12,
                      worldToScreenY(pts[i]->y) - 12, 25, 25};
        SDL_RenderCopy(ren, icons[i], NULL, &r);
        SDL_Surface *s = TTF_RenderText_Blended(smallFont, labels[i],
                                                (SDL_Color){255, 0, 0, 255});
        SDL_Texture *t = SDL_CreateTextureFromSurface(ren, s);
        SDL_Rect tr = {worldToScreenX(pts[i]->x) + 8,
                       worldToScreenY(pts[i]->y) - 20, s->w, s->h};
        SDL_RenderCopy(ren, t, NULL, &tr);
        SDL_FreeSurface(s);
        SDL_DestroyTexture(t);
      }
    }

    if (p1.valid || p2.valid) {
      char coords[256];
      // Display pixel coordinates only
      int px1 = (int)worldToPixelX(p1.x), py1 = (int)worldToPixelY(p1.y);
      int px2 = (int)worldToPixelX(p2.x), py2 = (int)worldToPixelY(p2.y);
      snprintf(coords, sizeof(coords), "A: (%d, %d) B: (%d, %d) | %s", px1, py1,
               px2, py2, infoText);
      SDL_Surface *cs =
          TTF_RenderText_Blended(font, coords, (SDL_Color){255, 255, 0, 255});
      SDL_Texture *ct = SDL_CreateTextureFromSurface(ren, cs);
      SDL_Rect cr = {10, 12, cs->w, cs->h};
      SDL_RenderCopy(ren, ct, NULL, &cr);
      SDL_FreeSurface(cs);
      SDL_DestroyTexture(ct);
    }

    // --- Route Analysis Panel ---
    SDL_SetRenderDrawBlendMode(ren, SDL_BLENDMODE_BLEND);
    SDL_Rect panel = {currW - 320, 210, 300, 280}; // Moved down 200px total

    // Draw rounded panel (no glossy effect)
    drawRoundedRect(ren, panel, 12, (SDL_Color){10, 27, 46, 240}, 0);

    // Draw rounded border stroke
    drawRoundedRectBorder(ren, panel, 12, (SDL_Color){0, 180, 200, 255});

    int yPos = panel.y + 15;

    // Title: "ROUTE ANALYSIS" with cyan indicator dot
    SDL_SetRenderDrawColor(ren, 0, 255, 255, 255);
    SDL_Rect dot = {panel.x + panel.w - 20, yPos + 5, 8, 8};
    SDL_RenderFillRect(ren, &dot);

    SDL_Surface *titleSurf = TTF_RenderText_Blended(
        titleFont, "ROUTE ANALYSIS", (SDL_Color){0, 255, 255, 255});
    SDL_Texture *titleTex = SDL_CreateTextureFromSurface(ren, titleSurf);
    SDL_Rect titleRect = {panel.x + 15, yPos, titleSurf->w, titleSurf->h};
    SDL_RenderCopy(ren, titleTex, NULL, &titleRect);
    SDL_FreeSurface(titleSurf);
    SDL_DestroyTexture(titleTex);
    yPos += 35;

    // Status
    SDL_Surface *statusLabel = TTF_RenderText_Blended(
        labelFont, "Status", (SDL_Color){150, 150, 150, 255});
    SDL_Texture *statusLabelTex =
        SDL_CreateTextureFromSurface(ren, statusLabel);
    SDL_Rect statusLabelRect = {panel.x + 15, yPos, statusLabel->w,
                                statusLabel->h};
    SDL_RenderCopy(ren, statusLabelTex, NULL, &statusLabelRect);
    SDL_FreeSurface(statusLabel);
    SDL_DestroyTexture(statusLabelTex);

    SDL_Color statusColor = strcmp(routeStatus, "OPTIMIZED") == 0
                                ? (SDL_Color){0, 255, 100, 255}
                                : (SDL_Color){255, 200, 0, 255};
    SDL_Surface *statusVal =
        TTF_RenderText_Blended(valueFont, routeStatus, statusColor);
    SDL_Texture *statusValTex = SDL_CreateTextureFromSurface(ren, statusVal);
    SDL_Rect statusValRect = {panel.x + panel.w - 15 - statusVal->w, yPos - 2,
                              statusVal->w, statusVal->h};
    SDL_RenderCopy(ren, statusValTex, NULL, &statusValRect);
    SDL_FreeSurface(statusVal);
    SDL_DestroyTexture(statusValTex);
    yPos += 35;

    // Total Distance
    SDL_Surface *distLabel = TTF_RenderText_Blended(
        labelFont, "Total Distance", (SDL_Color){150, 150, 150, 255});
    SDL_Texture *distLabelTex = SDL_CreateTextureFromSurface(ren, distLabel);
    SDL_Rect distLabelRect = {panel.x + 15, yPos, distLabel->w, distLabel->h};
    SDL_RenderCopy(ren, distLabelTex, NULL, &distLabelRect);
    SDL_FreeSurface(distLabel);
    SDL_DestroyTexture(distLabelTex);

    char distStr[64];
    snprintf(distStr, sizeof(distStr), "%.0f", routeDistance);
    SDL_Surface *distVal = TTF_RenderText_Blended(
        valueFont, distStr, (SDL_Color){255, 255, 255, 255});
    SDL_Texture *distValTex = SDL_CreateTextureFromSurface(ren, distVal);
    SDL_Rect distValRect = {panel.x + panel.w - 70 - distVal->w, yPos - 2,
                            distVal->w, distVal->h};
    SDL_RenderCopy(ren, distValTex, NULL, &distValRect);
    SDL_FreeSurface(distVal);
    SDL_DestroyTexture(distValTex);

    SDL_Surface *kmLabel = TTF_RenderText_Blended(
        labelFont, "km", (SDL_Color){100, 100, 100, 255});
    SDL_Texture *kmLabelTex = SDL_CreateTextureFromSurface(ren, kmLabel);
    SDL_Rect kmLabelRect = {panel.x + panel.w - 40, yPos, kmLabel->w,
                            kmLabel->h};
    SDL_RenderCopy(ren, kmLabelTex, NULL, &kmLabelRect);
    SDL_FreeSurface(kmLabel);
    SDL_DestroyTexture(kmLabelTex);
    yPos += 35;

    // ETA
    SDL_Surface *etaLabel = TTF_RenderText_Blended(
        labelFont, "ETA", (SDL_Color){150, 150, 150, 255});
    SDL_Texture *etaLabelTex = SDL_CreateTextureFromSurface(ren, etaLabel);
    SDL_Rect etaLabelRect = {panel.x + 15, yPos, etaLabel->w, etaLabel->h};
    SDL_RenderCopy(ren, etaLabelTex, NULL, &etaLabelRect);
    SDL_FreeSurface(etaLabel);
    SDL_DestroyTexture(etaLabelTex);

    char etaStr[64];
    snprintf(etaStr, sizeof(etaStr), "%.1f", routeETA);
    SDL_Surface *etaVal = TTF_RenderText_Blended(valueFont, etaStr,
                                                 (SDL_Color){0, 255, 255, 255});
    SDL_Texture *etaValTex = SDL_CreateTextureFromSurface(ren, etaVal);
    SDL_Rect etaValRect = {panel.x + panel.w - 80 - etaVal->w, yPos - 2,
                           etaVal->w, etaVal->h};
    SDL_RenderCopy(ren, etaValTex, NULL, &etaValRect);
    SDL_FreeSurface(etaVal);
    SDL_DestroyTexture(etaValTex);

    SDL_Surface *daysLabel = TTF_RenderText_Blended(
        labelFont, "days", (SDL_Color){100, 100, 100, 255});
    SDL_Texture *daysLabelTex = SDL_CreateTextureFromSurface(ren, daysLabel);
    SDL_Rect daysLabelRect = {panel.x + panel.w - 55, yPos, daysLabel->w,
                              daysLabel->h};
    SDL_RenderCopy(ren, daysLabelTex, NULL, &daysLabelRect);
    SDL_FreeSurface(daysLabel);
    SDL_DestroyTexture(daysLabelTex);
    yPos += 40;

    // Divider line
    SDL_SetRenderDrawColor(ren, 40, 60, 80, 255);
    SDL_RenderDrawLine(ren, panel.x + 15, yPos, panel.x + panel.w - 15, yPos);
    yPos += 15;

    // Fuel Estimate
    SDL_Surface *fuelLabel = TTF_RenderText_Blended(
        labelFont, "Fuel Estimate", (SDL_Color){0, 180, 200, 255});
    SDL_Texture *fuelLabelTex = SDL_CreateTextureFromSurface(ren, fuelLabel);
    SDL_Rect fuelLabelRect = {panel.x + 20, yPos, fuelLabel->w, fuelLabel->h};
    SDL_RenderCopy(ren, fuelLabelTex, NULL, &fuelLabelRect);
    SDL_FreeSurface(fuelLabel);
    SDL_DestroyTexture(fuelLabelTex);

    char fuelStr[64];
    snprintf(fuelStr, sizeof(fuelStr), "%.1f tons", routeFuel);
    SDL_Surface *fuelVal = TTF_RenderText_Blended(
        valueFont, fuelStr, (SDL_Color){200, 200, 200, 255});
    SDL_Texture *fuelValTex = SDL_CreateTextureFromSurface(ren, fuelVal);
    SDL_Rect fuelValRect = {panel.x + panel.w - 15 - fuelVal->w, yPos,
                            fuelVal->w, fuelVal->h};
    SDL_RenderCopy(ren, fuelValTex, NULL, &fuelValRect);
    SDL_FreeSurface(fuelVal);
    SDL_DestroyTexture(fuelValTex);
    yPos += 25;

    // Max Risk
    SDL_Surface *riskLabel = TTF_RenderText_Blended(
        labelFont, "Max Risk", (SDL_Color){0, 180, 200, 255});
    SDL_Texture *riskLabelTex = SDL_CreateTextureFromSurface(ren, riskLabel);
    SDL_Rect riskLabelRect = {panel.x + 20, yPos, riskLabel->w, riskLabel->h};
    SDL_RenderCopy(ren, riskLabelTex, NULL, &riskLabelRect);
    SDL_FreeSurface(riskLabel);
    SDL_DestroyTexture(riskLabelTex);

    char riskStr[64];
    snprintf(riskStr, sizeof(riskStr), "%.0f%%", routeRisk);
    SDL_Surface *riskVal = TTF_RenderText_Blended(
        valueFont, riskStr, (SDL_Color){0, 255, 100, 255});
    SDL_Texture *riskValTex = SDL_CreateTextureFromSurface(ren, riskVal);
    SDL_Rect riskValRect = {panel.x + panel.w - 15 - riskVal->w, yPos,
                            riskVal->w, riskVal->h};
    SDL_RenderCopy(ren, riskValTex, NULL, &riskValRect);
    SDL_FreeSurface(riskVal);
    SDL_DestroyTexture(riskValTex);
    yPos += 30;

    // Optimization note
    if (strcmp(routeStatus, "OPTIMIZED") == 0) {
      char noteStr[128];
      snprintf(noteStr, sizeof(noteStr), "*V5 Optimized: %.0fkm*",
               routeDistance);
      SDL_Surface *note = TTF_RenderText_Blended(
          labelFont, noteStr, (SDL_Color){100, 120, 140, 255});
      SDL_Texture *noteTex = SDL_CreateTextureFromSurface(ren, note);
      SDL_Rect noteRect = {panel.x + 15, yPos, note->w, note->h};
      SDL_RenderCopy(ren, noteTex, NULL, &noteRect);
      SDL_FreeSurface(note);
      SDL_DestroyTexture(noteTex);
    }

    // --- Mouse Coordinate Panel (Bottom Right) ---
    // --- Coordinate Panel (A / B) ---

    char coordA[128] = "A: --";
    char coordB[128] = "B: --";

    if (p1.valid) {
      float px = worldToPixelX(p1.x);
      float py = worldToPixelY(p1.y);
      float lat = pixelToLat(py);
      float lon = pixelToLon(px);
      char tmp[96];
      formatCoord(tmp, sizeof(tmp), lat, lon);
      snprintf(coordA, sizeof(coordA), "A: %s", tmp);
    }

    if (p2.valid) {
      float px = worldToPixelX(p2.x);
      float py = worldToPixelY(p2.y);
      float lat = pixelToLat(py);
      float lon = pixelToLon(px);
      char tmp[96];
      formatCoord(tmp, sizeof(tmp), lat, lon);
      snprintf(coordB, sizeof(coordB), "B: %s", tmp);
    }

    SDL_Surface *aSurf = TTF_RenderText_Blended(valueFont, coordA,
                                                (SDL_Color){0, 255, 255, 255});
    SDL_Surface *bSurf = TTF_RenderText_Blended(valueFont, coordB,
                                                (SDL_Color){0, 255, 255, 255});

    int panelW = (aSurf->w > bSurf->w ? aSurf->w : bSurf->w) + 30;
    int panelH = aSurf->h + bSurf->h + 30;

    int panelX = currW - panelW - 20;
    int panelY = currH - panelH - 20;

    SDL_Rect coordPanel = {panelX, panelY, panelW, panelH};
    drawRoundedRect(ren, coordPanel, 8, (SDL_Color){10, 27, 46, 240}, 0);
    drawRoundedRectBorder(ren, coordPanel, 8, (SDL_Color){0, 180, 200, 255});

    SDL_Texture *aTex = SDL_CreateTextureFromSurface(ren, aSurf);
    SDL_Texture *bTex = SDL_CreateTextureFromSurface(ren, bSurf);

    SDL_Rect aRect = {panelX + 15, panelY + 10, aSurf->w, aSurf->h};
    SDL_Rect bRect = {panelX + 15, panelY + 15 + aSurf->h, bSurf->w, bSurf->h};

    SDL_RenderCopy(ren, aTex, NULL, &aRect);
    SDL_RenderCopy(ren, bTex, NULL, &bRect);

    SDL_FreeSurface(aSurf);
    SDL_FreeSurface(bSurf);
    SDL_DestroyTexture(aTex);
    SDL_DestroyTexture(bTex);

    // vessel info panel
    // --- Vessel Info Panel (Table Style) ---
    int vesselPanelW = 300; // same width as ROUTE ANALYSIS panel
    int vesselPanelH = 90;
    int vesselPanelX = currW - vesselPanelW - 20; // right aligned
    int vesselPanelY = 100;                       // below top

    SDL_Rect vesselPanel = {vesselPanelX, vesselPanelY, vesselPanelW,
                            vesselPanelH};

    drawRoundedRect(ren, vesselPanel, 12, (SDL_Color){10, 27, 46, 240}, 0);
    drawRoundedRectBorder(ren, vesselPanel, 12, (SDL_Color){0, 180, 200, 255});

    // Column X positions
    int colVessel = vesselPanel.x + 15;
    int colSpeed = vesselPanel.x + 120;
    int colMode = vesselPanel.x + 200;

    // Header row
    SDL_Surface *hVessel = TTF_RenderText_Blended(
        labelFont, "VESSEL", (SDL_Color){120, 180, 200, 255});
    SDL_Surface *hSpeed = TTF_RenderText_Blended(
        labelFont, "SPEED", (SDL_Color){120, 180, 200, 255});
    SDL_Surface *hMode = TTF_RenderText_Blended(
        labelFont, "MODE", (SDL_Color){120, 180, 200, 255});

    SDL_Texture *hVesselT = SDL_CreateTextureFromSurface(ren, hVessel);
    SDL_Texture *hSpeedT = SDL_CreateTextureFromSurface(ren, hSpeed);
    SDL_Texture *hModeT = SDL_CreateTextureFromSurface(ren, hMode);

    SDL_RenderCopy(
        ren, hVesselT, NULL,
        &(SDL_Rect){colVessel, vesselPanel.y + 10, hVessel->w, hVessel->h});
    SDL_RenderCopy(
        ren, hSpeedT, NULL,
        &(SDL_Rect){colSpeed, vesselPanel.y + 10, hSpeed->w, hSpeed->h});
    SDL_RenderCopy(
        ren, hModeT, NULL,
        &(SDL_Rect){colMode, vesselPanel.y + 10, hMode->w, hMode->h});

    SDL_FreeSurface(hVessel);
    SDL_FreeSurface(hSpeed);
    SDL_FreeSurface(hMode);
    SDL_DestroyTexture(hVesselT);
    SDL_DestroyTexture(hSpeedT);
    SDL_DestroyTexture(hModeT);

    // Divider line
    SDL_SetRenderDrawColor(ren, 40, 70, 90, 255);
    SDL_RenderDrawLine(ren, vesselPanel.x + 15, vesselPanel.y + 38,
                       vesselPanel.x + vesselPanel.w - 15, vesselPanel.y + 38);

    // Value row
    SDL_Surface *vName = TTF_RenderText_Blended(
        smallFont, shipName, (SDL_Color){255, 255, 255, 255});
    SDL_Surface *vSpeed = TTF_RenderText_Blended(smallFont, shipSpeed,
                                                 (SDL_Color){0, 255, 255, 255});
    SDL_Surface *vMode = TTF_RenderText_Blended(smallFont, shipMode,
                                                (SDL_Color){0, 255, 100, 255});

    SDL_Texture *vNameT = SDL_CreateTextureFromSurface(ren, vName);
    SDL_Texture *vSpeedT = SDL_CreateTextureFromSurface(ren, vSpeed);
    SDL_Texture *vModeT = SDL_CreateTextureFromSurface(ren, vMode);

    SDL_RenderCopy(
        ren, vNameT, NULL,
        &(SDL_Rect){colVessel, vesselPanel.y + 45, vName->w, vName->h});
    SDL_RenderCopy(
        ren, vSpeedT, NULL,
        &(SDL_Rect){colSpeed, vesselPanel.y + 45, vSpeed->w, vSpeed->h});
    SDL_RenderCopy(
        ren, vModeT, NULL,
        &(SDL_Rect){colMode, vesselPanel.y + 45, vMode->w, vMode->h});

    SDL_FreeSurface(vName);
    SDL_FreeSurface(vSpeed);
    SDL_FreeSurface(vMode);
    SDL_DestroyTexture(vNameT);
    SDL_DestroyTexture(vSpeedT);
    SDL_DestroyTexture(vModeT);

    SDL_RenderPresent(ren);
  }
  TTF_CloseFont(font);
  TTF_CloseFont(smallFont);
  SDL_Quit();
  return 0;
}
