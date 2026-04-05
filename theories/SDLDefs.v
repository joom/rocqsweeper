(** * Shared SDL effect definitions.

    Contains the SDL handle types, generic SDL input types, the SDL effect
    functor, and smart constructors that are independent of extraction flavor.
    [SDL.v] re-exports this module and adds the C++ extraction mappings. *)

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

(** The SDL keys recognized explicitly in the generic Rocq event layer. *)
Inductive sdl_key : Type :=
| KeyEscape | KeyReturn | KeySpace | KeyTab | KeyBackspace
| KeyInsert | KeyDelete | KeyHome | KeyEnd | KeyPageUp | KeyPageDown
| KeyUp | KeyDown | KeyLeft | KeyRight
| KeyShift | KeyCtrl | KeyAlt | KeyGui
| KeyComma | KeyPeriod | KeySlash | KeySemicolon | KeyQuote
| KeyLeftBracket | KeyRightBracket | KeyBackslash
| KeyMinus | KeyEquals | KeyBackquote
| KeyCapsLock | KeyNumLock | KeyScrollLock
| KeyPrintScreen | KeyPause | KeyMenu
| KeyF1 | KeyF2 | KeyF3 | KeyF4 | KeyF5 | KeyF6
| KeyF7 | KeyF8 | KeyF9 | KeyF10 | KeyF11 | KeyF12
| KeyA | KeyB | KeyC | KeyD | KeyE | KeyF | KeyG | KeyH | KeyI | KeyJ | KeyK
| KeyL | KeyM | KeyN | KeyO | KeyP | KeyQ | KeyR | KeyS | KeyT | KeyU | KeyV
| KeyW | KeyX | KeyY | KeyZ
| KeyDigit0 | KeyDigit1 | KeyDigit2 | KeyDigit3 | KeyDigit4
| KeyDigit5 | KeyDigit6 | KeyDigit7 | KeyDigit8 | KeyDigit9
| KeyOther : nat -> sdl_key.

(** Mouse button identifiers recognized by the generic Rocq event layer. *)
Inductive sdl_mouse_button : Type :=
| MouseLeft | MouseMiddle | MouseRight | MouseX1 | MouseX2
| MouseOther : nat -> sdl_mouse_button.

(** Generic SDL events surfaced to Rocq code. *)
Inductive sdl_event : Type :=
| EventNone
| EventQuit
| EventKeyDown : sdl_key -> sdl_event
| EventKeyUp : sdl_key -> sdl_event
| EventMouseMotion : nat * nat -> sdl_event
| EventMouseButtonDown : sdl_mouse_button -> nat * nat -> sdl_event
| EventMouseButtonUp : sdl_mouse_button -> nat * nat -> sdl_event.

(** Base value used by SDL for scancode-derived keycodes. *)
Definition sdl_scancode_mask : nat := Nat.pow 2 30.

(** SDL keycode for the up arrow. *)
Definition sdl_keycode_up : nat := sdl_scancode_mask + 82.
(** SDL keycode for the down arrow. *)
Definition sdl_keycode_down : nat := sdl_scancode_mask + 81.
(** SDL keycode for the left arrow. *)
Definition sdl_keycode_left : nat := sdl_scancode_mask + 80.
(** SDL keycode for the right arrow. *)
Definition sdl_keycode_right : nat := sdl_scancode_mask + 79.
(** SDL keycode for Insert. *)
Definition sdl_keycode_insert : nat := sdl_scancode_mask + 73.
(** SDL keycode for Home. *)
Definition sdl_keycode_home : nat := sdl_scancode_mask + 74.
(** SDL keycode for PageUp. *)
Definition sdl_keycode_pageup : nat := sdl_scancode_mask + 75.
(** SDL keycode for Delete. *)
Definition sdl_keycode_delete : nat := sdl_scancode_mask + 76.
(** SDL keycode for End. *)
Definition sdl_keycode_end : nat := sdl_scancode_mask + 77.
(** SDL keycode for PageDown. *)
Definition sdl_keycode_pagedown : nat := sdl_scancode_mask + 78.
(** SDL keycode for F1. *)
Definition sdl_keycode_f1 : nat := sdl_scancode_mask + 58.
(** SDL keycode for F2. *)
Definition sdl_keycode_f2 : nat := sdl_scancode_mask + 59.
(** SDL keycode for F3. *)
Definition sdl_keycode_f3 : nat := sdl_scancode_mask + 60.
(** SDL keycode for F4. *)
Definition sdl_keycode_f4 : nat := sdl_scancode_mask + 61.
(** SDL keycode for F5. *)
Definition sdl_keycode_f5 : nat := sdl_scancode_mask + 62.
(** SDL keycode for F6. *)
Definition sdl_keycode_f6 : nat := sdl_scancode_mask + 63.
(** SDL keycode for F7. *)
Definition sdl_keycode_f7 : nat := sdl_scancode_mask + 64.
(** SDL keycode for F8. *)
Definition sdl_keycode_f8 : nat := sdl_scancode_mask + 65.
(** SDL keycode for F9. *)
Definition sdl_keycode_f9 : nat := sdl_scancode_mask + 66.
(** SDL keycode for F10. *)
Definition sdl_keycode_f10 : nat := sdl_scancode_mask + 67.
(** SDL keycode for F11. *)
Definition sdl_keycode_f11 : nat := sdl_scancode_mask + 68.
(** SDL keycode for F12. *)
Definition sdl_keycode_f12 : nat := sdl_scancode_mask + 69.
(** SDL keycode for CapsLock. *)
Definition sdl_keycode_capslock : nat := sdl_scancode_mask + 57.
(** SDL keycode for PrintScreen. *)
Definition sdl_keycode_printscreen : nat := sdl_scancode_mask + 70.
(** SDL keycode for ScrollLock. *)
Definition sdl_keycode_scrolllock : nat := sdl_scancode_mask + 71.
(** SDL keycode for Pause. *)
Definition sdl_keycode_pause : nat := sdl_scancode_mask + 72.
(** SDL keycode for NumLock. *)
Definition sdl_keycode_numlock : nat := sdl_scancode_mask + 83.
(** SDL keycode for Menu. *)
Definition sdl_keycode_menu : nat := sdl_scancode_mask + 118.
(** SDL keycode for left shift. *)
Definition sdl_keycode_lshift : nat := sdl_scancode_mask + 225.
(** SDL keycode for right shift. *)
Definition sdl_keycode_rshift : nat := sdl_scancode_mask + 229.
(** SDL keycode for left ctrl. *)
Definition sdl_keycode_lctrl : nat := sdl_scancode_mask + 224.
(** SDL keycode for right ctrl. *)
Definition sdl_keycode_rctrl : nat := sdl_scancode_mask + 228.
(** SDL keycode for left alt. *)
Definition sdl_keycode_lalt : nat := sdl_scancode_mask + 226.
(** SDL keycode for right alt. *)
Definition sdl_keycode_ralt : nat := sdl_scancode_mask + 230.
(** SDL keycode for left GUI / command. *)
Definition sdl_keycode_lgui : nat := sdl_scancode_mask + 227.
(** SDL keycode for right GUI / command. *)
Definition sdl_keycode_rgui : nat := sdl_scancode_mask + 231.

(** Decode a raw SDL keycode into the generic Rocq key type. *)
Definition decode_sdl_key (code : nat) : sdl_key :=
  match code with
  | 8 => KeyBackspace
  | 9 => KeyTab
  | 13 => KeyReturn
  | 27 => KeyEscape
  | 32 => KeySpace
  | 39 => KeyQuote
  | 44 => KeyComma
  | 45 => KeyMinus
  | 46 => KeyPeriod
  | 47 => KeySlash
  | 48 => KeyDigit0
  | 49 => KeyDigit1
  | 50 => KeyDigit2
  | 51 => KeyDigit3
  | 52 => KeyDigit4
  | 53 => KeyDigit5
  | 54 => KeyDigit6
  | 55 => KeyDigit7
  | 56 => KeyDigit8
  | 57 => KeyDigit9
  | 59 => KeySemicolon
  | 61 => KeyEquals
  | 91 => KeyLeftBracket
  | 92 => KeyBackslash
  | 93 => KeyRightBracket
  | 97 => KeyA
  | 96 => KeyBackquote
  | 98 => KeyB
  | 99 => KeyC
  | 100 => KeyD
  | 101 => KeyE
  | 102 => KeyF
  | 103 => KeyG
  | 104 => KeyH
  | 105 => KeyI
  | 106 => KeyJ
  | 107 => KeyK
  | 108 => KeyL
  | 109 => KeyM
  | 110 => KeyN
  | 111 => KeyO
  | 112 => KeyP
  | 113 => KeyQ
  | 114 => KeyR
  | 115 => KeyS
  | 116 => KeyT
  | 117 => KeyU
  | 118 => KeyV
  | 119 => KeyW
  | 120 => KeyX
  | 121 => KeyY
  | 122 => KeyZ
  | _ =>
      if Nat.eqb code sdl_keycode_insert then KeyInsert
      else if Nat.eqb code sdl_keycode_delete then KeyDelete
      else if Nat.eqb code sdl_keycode_home then KeyHome
      else if Nat.eqb code sdl_keycode_end then KeyEnd
      else if Nat.eqb code sdl_keycode_pageup then KeyPageUp
      else if Nat.eqb code sdl_keycode_pagedown then KeyPageDown
      else if Nat.eqb code sdl_keycode_up then KeyUp
      else if Nat.eqb code sdl_keycode_down then KeyDown
      else if Nat.eqb code sdl_keycode_left then KeyLeft
      else if Nat.eqb code sdl_keycode_right then KeyRight
      else if orb (Nat.eqb code sdl_keycode_lshift) (Nat.eqb code sdl_keycode_rshift) then KeyShift
      else if orb (Nat.eqb code sdl_keycode_lctrl) (Nat.eqb code sdl_keycode_rctrl) then KeyCtrl
      else if orb (Nat.eqb code sdl_keycode_lalt) (Nat.eqb code sdl_keycode_ralt) then KeyAlt
      else if orb (Nat.eqb code sdl_keycode_lgui) (Nat.eqb code sdl_keycode_rgui) then KeyGui
      else if Nat.eqb code sdl_keycode_capslock then KeyCapsLock
      else if Nat.eqb code sdl_keycode_numlock then KeyNumLock
      else if Nat.eqb code sdl_keycode_scrolllock then KeyScrollLock
      else if Nat.eqb code sdl_keycode_printscreen then KeyPrintScreen
      else if Nat.eqb code sdl_keycode_pause then KeyPause
      else if Nat.eqb code sdl_keycode_menu then KeyMenu
      else if Nat.eqb code sdl_keycode_f1 then KeyF1
      else if Nat.eqb code sdl_keycode_f2 then KeyF2
      else if Nat.eqb code sdl_keycode_f3 then KeyF3
      else if Nat.eqb code sdl_keycode_f4 then KeyF4
      else if Nat.eqb code sdl_keycode_f5 then KeyF5
      else if Nat.eqb code sdl_keycode_f6 then KeyF6
      else if Nat.eqb code sdl_keycode_f7 then KeyF7
      else if Nat.eqb code sdl_keycode_f8 then KeyF8
      else if Nat.eqb code sdl_keycode_f9 then KeyF9
      else if Nat.eqb code sdl_keycode_f10 then KeyF10
      else if Nat.eqb code sdl_keycode_f11 then KeyF11
      else if Nat.eqb code sdl_keycode_f12 then KeyF12
      else KeyOther code
  end.

(** Decode a raw SDL mouse button code into the generic Rocq button type. *)
Definition decode_sdl_mouse_button (code : nat) : sdl_mouse_button :=
  match code with
  | 1 => MouseLeft
  | 2 => MouseMiddle
  | 3 => MouseRight
  | 4 => MouseX1
  | 5 => MouseX2
  | _ => MouseOther code
  end.

(** Decode a raw event kind together with auxiliary fields into a generic event. *)
Definition decode_sdl_event (kind keycode button x y : nat) : sdl_event :=
  let pos := (x, y) in
  match kind with
  | 0 => EventNone
  | 1 => EventQuit
  | 2 => EventKeyDown (decode_sdl_key keycode)
  | 3 => EventKeyUp (decode_sdl_key keycode)
  | 4 => EventMouseMotion pos
  | 5 => EventMouseButtonDown (decode_sdl_mouse_button button) pos
  | 6 => EventMouseButtonUp (decode_sdl_mouse_button button) pos
  | _ => EventNone
  end.

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
| PollEvent : sdlE sdl_event
| GetMousePosition : sdlE (nat * nat)
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

(** Poll the next SDL event. *)
Definition sdl_poll_event : itree sdlE sdl_event :=
  embed PollEvent.

(** Read the current mouse position in window coordinates. *)
Definition sdl_get_mouse_position : itree sdlE (nat * nat) :=
  embed GetMousePosition.

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
