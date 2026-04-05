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

namespace {
inline unsigned int &sdl_last_key_code_ref() {
  static unsigned int code = 0;
  return code;
}

inline unsigned int &sdl_last_mouse_button_ref() {
  static unsigned int button = 0;
  return button;
}

inline unsigned int &sdl_last_mouse_x_ref() {
  static unsigned int x = 0;
  return x;
}

inline unsigned int &sdl_last_mouse_y_ref() {
  static unsigned int y = 0;
  return y;
}

inline void sdl_store_mouse_position(int x, int y) {
  sdl_last_mouse_x_ref() = x < 0 ? 0u : (unsigned int)x;
  sdl_last_mouse_y_ref() = y < 0 ? 0u : (unsigned int)y;
}
}

// current mouse position in window coordinates
inline unsigned int sdl_last_mouse_x() {
  int x = 0;
  int y = 0;
  SDL_GetMouseState(&x, &y);
  sdl_store_mouse_position(x, y);
  return sdl_last_mouse_x_ref();
}

inline unsigned int sdl_last_mouse_y() {
  int x = 0;
  int y = 0;
  SDL_GetMouseState(&x, &y);
  sdl_store_mouse_position(x, y);
  return sdl_last_mouse_y_ref();
}

// last decoded SDL key code from event polling
inline unsigned int sdl_last_key_code() {
  return sdl_last_key_code_ref();
}

// last decoded SDL mouse button from event polling
inline unsigned int sdl_last_mouse_button() {
  return sdl_last_mouse_button_ref();
}

// event polling
// Returns:
// 0=none, 1=quit, 2=key-down, 3=key-up, 4=mouse-motion,
// 5=mouse-button-down, 6=mouse-button-up
inline unsigned int sdl_poll_event_kind() {
  SDL_Event ev;
  while (SDL_PollEvent(&ev)) {
    switch (ev.type) {
    case SDL_QUIT:
      return 1;
    case SDL_KEYDOWN:
      sdl_last_key_code_ref() = (unsigned int)ev.key.keysym.sym;
      return 2;
    case SDL_KEYUP:
      sdl_last_key_code_ref() = (unsigned int)ev.key.keysym.sym;
      return 3;
    case SDL_MOUSEMOTION:
      sdl_store_mouse_position(ev.motion.x, ev.motion.y);
      return 4;
    case SDL_MOUSEBUTTONDOWN:
      sdl_last_mouse_button_ref() = (unsigned int)ev.button.button;
      sdl_store_mouse_position(ev.button.x, ev.button.y);
      return 5;
    case SDL_MOUSEBUTTONUP:
      sdl_last_mouse_button_ref() = (unsigned int)ev.button.button;
      sdl_store_mouse_position(ev.button.x, ev.button.y);
      return 6;
    default:
      break;
    }
  }
  return 0;
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
