(** * Shared SDL effect definitions.

    Contains the SDL handle types, the SDL event functor, and smart
    constructors that are independent of extraction flavor. [SDL.v]
    re-exports this module and adds the C++ extraction mappings. *)

From Corelib Require Import PrimString.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

(** Convert a natural number to its decimal digits using a fuel argument
    to keep the recursion structurally decreasing. *)
Fixpoint nat_digit_list_aux (fuel n : nat) : list nat :=
  match fuel with
  | 0 => [0]
  | S fuel' =>
    let q := Nat.div n 10 in
    let d := Nat.modulo n 10 in
    if Nat.ltb q 1
    then [d]
    else nat_digit_list_aux fuel' q ++ [d]
  end.

(** Convert a natural number to its list of decimal digits
    (most significant digit first). *)
Definition nat_digit_list (n : nat) : list nat :=
  nat_digit_list_aux n n.

(** An opaque SDL window handle. *)
Axiom sdl_window : Type.

(** An opaque SDL renderer handle. *)
Axiom sdl_renderer : Type.

(** An opaque SDL texture handle. *)
Axiom sdl_texture : Type.

(** SDL operations used by the extracted game loop. *)
Inductive sdlE : Type -> Type :=
| CreateWindow : PrimString.string -> nat -> nat -> sdlE sdl_window
| CreateRenderer : sdl_window -> sdlE sdl_renderer
| Destroy : sdl_renderer -> sdl_window -> sdlE void
| SetDrawColor : sdl_renderer -> nat -> nat -> nat -> sdlE void
| Clear : sdl_renderer -> sdlE void
| Present : sdl_renderer -> sdlE void
| FillRect : sdl_renderer -> nat -> nat -> nat -> nat -> sdlE void
| DrawPoint : sdl_renderer -> nat -> nat -> sdlE void
| PollEvent : sdlE nat
| GetMouseX : sdlE nat
| GetMouseY : sdlE nat
| GetTicks : sdlE nat
| Delay : nat -> sdlE void
| LoadTexture : sdl_renderer -> PrimString.string -> sdlE sdl_texture
| PlaySound : PrimString.string -> sdlE void
| RenderTextureRotated : sdl_renderer -> sdl_texture ->
    nat -> nat -> nat -> nat -> nat -> bool -> sdlE void.

(** Skip extraction for the abstract SDL effect functor itself. *)
Crane Extract Skip sdlE.


(** Create a window with the given title, width, and height. *)
Definition sdl_create_window {E} `{sdlE -< E}
    (title : PrimString.string) (w h : nat) : itree E sdl_window :=
  embed (CreateWindow title w h).

(** Create a hardware-accelerated, vsync-enabled renderer. *)
Definition sdl_create_renderer {E} `{sdlE -< E}
    (win : sdl_window) : itree E sdl_renderer :=
  embed (CreateRenderer win).

(** Destroy the renderer and window, then quit SDL. *)
Definition sdl_destroy {E} `{sdlE -< E}
    (ren : sdl_renderer) (win : sdl_window) : itree E void :=
  embed (Destroy ren win).

(** Set the current draw color (RGB, alpha is always 255). *)
Definition sdl_set_draw_color {E} `{sdlE -< E}
    (ren : sdl_renderer) (r g b : nat) : itree E void :=
  embed (SetDrawColor ren r g b).

(** Clear the renderer with the current draw color. *)
Definition sdl_clear {E} `{sdlE -< E}
    (ren : sdl_renderer) : itree E void :=
  embed (Clear ren).

(** Present the renderer (flip the back-buffer to screen). *)
Definition sdl_present {E} `{sdlE -< E}
    (ren : sdl_renderer) : itree E void :=
  embed (Present ren).

(** Fill a rectangle at [(x, y)] with dimensions [(w, h)]. *)
Definition sdl_fill_rect {E} `{sdlE -< E}
    (ren : sdl_renderer) (x y w h : nat) : itree E void :=
  embed (FillRect ren x y w h).

(** Draw a single pixel at [(x, y)]. *)
Definition sdl_draw_point {E} `{sdlE -< E}
    (ren : sdl_renderer) (x y : nat) : itree E void :=
  embed (DrawPoint ren x y).

(** Poll the next abstract event code.
    Returns: 0=none, 1=quit, 2=up, 3=down, 4=left, 5=right,
    6=reveal, 7=flag, 8=restart, 9=left-click, 10=right-click. *)
Definition sdl_poll_event {E} `{sdlE -< E} : itree E nat :=
  embed PollEvent.

(** Get the current mouse x coordinate. *)
Definition sdl_get_mouse_x {E} `{sdlE -< E} : itree E nat :=
  embed GetMouseX.

(** Get the current mouse y coordinate. *)
Definition sdl_get_mouse_y {E} `{sdlE -< E} : itree E nat :=
  embed GetMouseY.

(** Get the number of milliseconds since SDL was initialized. *)
Definition sdl_get_ticks {E} `{sdlE -< E} : itree E nat :=
  embed GetTicks.

(** Pause execution for the given number of milliseconds. *)
Definition sdl_delay {E} `{sdlE -< E} (ms : nat) : itree E void :=
  embed (Delay ms).

(** Load an image file (PNG, SVG, etc.) as a texture via SDL_image. *)
Definition sdl_load_texture {E} `{sdlE -< E}
    (ren : sdl_renderer) (path : PrimString.string) : itree E sdl_texture :=
  embed (LoadTexture ren path).

(** Play an audio file asynchronously. *)
Definition sdl_play_sound {E} `{sdlE -< E}
    (path : PrimString.string) : itree E void :=
  embed (PlaySound path).

(** Render a texture centered at [(cx, cy)] with size [(w, h)],
    rotated by [angle] degrees clockwise and optionally mirrored on the y axis. *)
Definition sdl_render_texture_rotated {E} `{sdlE -< E}
    (ren : sdl_renderer) (tex : sdl_texture)
    (cx cy w h angle : nat) (flip_h : bool) : itree E void :=
  embed (RenderTextureRotated ren tex cx cy w h angle flip_h).
