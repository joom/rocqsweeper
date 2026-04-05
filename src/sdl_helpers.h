#pragma once
#include <SDL.h>
#include <SDL_image.h>
#include <SDL_mixer.h>
#include <cstdint>
#include <string>
#include <unordered_map>

// Opaque types for Rocq extraction
using sdl_window = SDL_Window*;
using sdl_renderer = SDL_Renderer*;
using sdl_texture = SDL_Texture*;

namespace {
inline bool &sdl_audio_ready() {
  static bool ready = false;
  return ready;
}

inline std::unordered_map<std::string, Mix_Chunk*> &sdl_sound_cache() {
  static std::unordered_map<std::string, Mix_Chunk*> cache;
  return cache;
}

inline void sdl_init_audio() {
  if (sdl_audio_ready()) return;
  if (SDL_InitSubSystem(SDL_INIT_AUDIO) != 0) return;
  if ((Mix_Init(MIX_INIT_MP3) & MIX_INIT_MP3) == 0) return;
  if (Mix_OpenAudio(44100, MIX_DEFAULT_FORMAT, 2, 2048) != 0) return;
  sdl_audio_ready() = true;
}

inline void sdl_shutdown_audio() {
  for (auto &entry : sdl_sound_cache()) {
    if (entry.second != nullptr) Mix_FreeChunk(entry.second);
  }
  sdl_sound_cache().clear();
  if (sdl_audio_ready()) {
    Mix_CloseAudio();
    Mix_Quit();
    sdl_audio_ready() = false;
  }
}
}

// SDL init / teardown
inline sdl_window sdl_create_window(const std::string &title,
                                    unsigned int w, unsigned int h) {
  if (SDL_Init(SDL_INIT_VIDEO) != 0) return nullptr;
  sdl_init_audio();
  return SDL_CreateWindow(title.c_str(), SDL_WINDOWPOS_CENTERED,
                          SDL_WINDOWPOS_CENTERED, (int)w, (int)h,
                          SDL_WINDOW_SHOWN);
}

inline sdl_renderer sdl_create_renderer(sdl_window win) {
  return SDL_CreateRenderer(
      win, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
}

inline void sdl_destroy(sdl_renderer ren, sdl_window win) {
  sdl_shutdown_audio();
  SDL_DestroyRenderer(ren);
  SDL_DestroyWindow(win);
  SDL_Quit();
}

// drawing primitives
inline void sdl_set_draw_color(sdl_renderer r,
                               unsigned int red, unsigned int green,
                               unsigned int blue) {
  SDL_SetRenderDrawColor(r, (uint8_t)red, (uint8_t)green, (uint8_t)blue, 255);
}

inline void sdl_clear(sdl_renderer r) {
  SDL_RenderClear(r);
}

inline void sdl_present(sdl_renderer r) {
  SDL_RenderPresent(r);
}

inline void sdl_fill_rect(sdl_renderer r,
                          unsigned int x, unsigned int y,
                          unsigned int w, unsigned int h) {
  SDL_Rect rect = {(int)x, (int)y, (int)w, (int)h};
  SDL_RenderFillRect(r, &rect);
}

inline void sdl_draw_point(sdl_renderer r,
                           unsigned int x, unsigned int y) {
  SDL_RenderDrawPoint(r, (int)x, (int)y);
}

// current mouse position in window coordinates
inline unsigned int sdl_last_mouse_x() {
  int x = 0;
  int y = 0;
  SDL_GetMouseState(&x, &y);
  (void)y;
  return x < 0 ? 0u : (unsigned int)x;
}

inline unsigned int sdl_last_mouse_y() {
  int x = 0;
  int y = 0;
  SDL_GetMouseState(&x, &y);
  (void)x;
  return y < 0 ? 0u : (unsigned int)y;
}

// event polling
// Returns:
// 0=none, 1=quit, 2=up, 3=down, 4=left, 5=right, 6=reveal, 7=flag, 8=restart,
// 9=left-click, 10=right-click
inline unsigned int sdl_poll_event() {
  SDL_Event ev;
  unsigned int result = 0;
  while (SDL_PollEvent(&ev)) {
    if (ev.type == SDL_QUIT) return 1;
    if (ev.type == SDL_MOUSEBUTTONDOWN) {
      if (ev.button.button == SDL_BUTTON_LEFT) return 9;
      if (ev.button.button == SDL_BUTTON_RIGHT) return 10;
    }
    if (ev.type == SDL_KEYDOWN) {
      switch (ev.key.keysym.sym) {
      case SDLK_ESCAPE:
      case SDLK_q:
        return 1;
      case SDLK_UP:
      case SDLK_w:
        result = 2;
        break;
      case SDLK_DOWN:
      case SDLK_s:
        result = 3;
        break;
      case SDLK_LEFT:
      case SDLK_a:
        result = 4;
        break;
      case SDLK_RIGHT:
      case SDLK_d:
        result = 5;
        break;
      case SDLK_SPACE:
        result = 6;
        break;
      case SDLK_f:
        result = 7;
        break;
      case SDLK_r:
        result = 8;
        break;
      default:
        break;
      }
    }
  }
  return result;
}

// timing
inline unsigned int sdl_get_ticks() {
  return (unsigned int)SDL_GetTicks();
}

inline void sdl_delay(unsigned int ms) {
  SDL_Delay(ms);
}

// textures
inline sdl_texture sdl_load_texture(sdl_renderer ren,
                                    const std::string &path) {
  SDL_Surface *surface = IMG_Load(path.c_str());
  if (!surface) return nullptr;
  SDL_Texture *tex = SDL_CreateTextureFromSurface(ren, surface);
  SDL_FreeSurface(surface);
  return tex;
}

inline void sdl_play_sound(const std::string &path) {
  if (path.empty()) return;
  sdl_init_audio();
  if (!sdl_audio_ready()) return;
  auto &cache = sdl_sound_cache();
  Mix_Chunk *chunk = nullptr;
  auto it = cache.find(path);
  if (it != cache.end()) {
    chunk = it->second;
  } else {
    chunk = Mix_LoadWAV(path.c_str());
    cache.emplace(path, chunk);
  }
  if (chunk != nullptr) Mix_PlayChannel(-1, chunk, 0);
}

inline void sdl_render_texture_rotated(sdl_renderer ren, sdl_texture tex,
                                       unsigned int cx, unsigned int cy,
                                       unsigned int w, unsigned int h,
                                       unsigned int angle_deg,
                                       bool flip_h) {
  SDL_Rect dst = {(int)(cx - w / 2), (int)(cy - h / 2), (int)w, (int)h};
  SDL_RendererFlip flip = flip_h ? SDL_FLIP_HORIZONTAL : SDL_FLIP_NONE;
  SDL_RenderCopyEx(ren, tex, nullptr, &dst,
                   (double)angle_deg, nullptr, flip);
}
