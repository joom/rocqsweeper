(** * SDL extraction mappings for the standard library flavor.

    Re-exports the shared SDL effect definitions from [SDLDefs.v] and maps
    them to the C++ helpers implemented in [sdl_helpers.h]. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From RocqsweeperGame Require Export SDLDefs.

(** Extract the opaque SDL window handle to the helper typedef. *)
Crane Extract Inlined Constant sdl_window => "sdl_window" From "sdl_helpers.h".

(** Extract the opaque SDL renderer handle to the helper typedef. *)
Crane Extract Inlined Constant sdl_renderer => "sdl_renderer" From "sdl_helpers.h".

(** Extract the opaque SDL texture handle to the helper typedef. *)
Crane Extract Inlined Constant sdl_texture => "sdl_texture" From "sdl_helpers.h".

(** Extract SDL effects to the corresponding helper calls. *)
Crane Extract Inductive sdlE => ""
  [ "sdl_create_window(%a0, %a1, %a2)"
    "sdl_create_renderer(%a0)"
    "sdl_destroy(%a0, %a1)"
    "sdl_set_draw_color(%a0, %a1, %a2, %a3)"
    "sdl_clear(%a0)"
    "sdl_present(%a0)"
    "sdl_fill_rect(%a0, %a1, %a2, %a3, %a4)"
    "sdl_draw_point(%a0, %a1, %a2)"
    "sdl_poll_event()"
    "sdl_last_mouse_x()"
    "sdl_last_mouse_y()"
    "sdl_get_ticks()"
    "sdl_delay(%a0)"
    "sdl_load_texture(%a0, %a1)"
    "sdl_play_sound(%a0)"
    "sdl_render_texture_rotated(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7)" ]
  From "sdl_helpers.h".

(** Extract the SDL smart constructors directly to helper calls. *)
Crane Extract Inlined Constant sdl_create_window =>
  "sdl_create_window(%a0, %a1, %a2)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_create_renderer =>
  "sdl_create_renderer(%a0)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_destroy =>
  "sdl_destroy(%a0, %a1)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_set_draw_color =>
  "sdl_set_draw_color(%a0, %a1, %a2, %a3)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_clear =>
  "sdl_clear(%a0)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_present =>
  "sdl_present(%a0)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_fill_rect =>
  "sdl_fill_rect(%a0, %a1, %a2, %a3, %a4)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_draw_point =>
  "sdl_draw_point(%a0, %a1, %a2)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_poll_event =>
  "sdl_poll_event()" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_get_mouse_x =>
  "sdl_last_mouse_x()" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_get_mouse_y =>
  "sdl_last_mouse_y()" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_get_ticks =>
  "sdl_get_ticks()" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_delay =>
  "sdl_delay(%a0)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_load_texture =>
  "sdl_load_texture(%a0, %a1)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_play_sound =>
  "sdl_play_sound(%a0)" From "sdl_helpers.h".
Crane Extract Inlined Constant sdl_render_texture_rotated =>
  "sdl_render_texture_rotated(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7)"
  From "sdl_helpers.h".
