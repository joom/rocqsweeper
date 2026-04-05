(** * SDL extraction mappings for the standard library flavor.

    Re-exports the shared SDL effect definitions from [SDLDefs.v] and maps
    them to the C++ helpers implemented in [sdl_helpers.h]. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.
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
    "([&]() -> std::shared_ptr<Sdl_event> { \
      const unsigned int kind = sdl_poll_event_kind(); \
      const unsigned int keycode = sdl_last_key_code(); \
      const unsigned int button = sdl_last_mouse_button(); \
      auto decode_key = [&](const unsigned int code) -> std::shared_ptr<Sdl_key> { \
        switch (code) { \
        case SDLK_BACKSPACE: return Sdl_key::keybackspace(); \
        case SDLK_TAB: return Sdl_key::keytab(); \
        case SDLK_RETURN: return Sdl_key::keyreturn(); \
        case SDLK_ESCAPE: return Sdl_key::keyescape(); \
        case SDLK_SPACE: return Sdl_key::keyspace(); \
        case SDLK_INSERT: return Sdl_key::keyinsert(); \
        case SDLK_DELETE: return Sdl_key::keydelete(); \
        case SDLK_HOME: return Sdl_key::keyhome(); \
        case SDLK_END: return Sdl_key::keyend(); \
        case SDLK_PAGEUP: return Sdl_key::keypageup(); \
        case SDLK_PAGEDOWN: return Sdl_key::keypagedown(); \
        case SDLK_LSHIFT: \
        case SDLK_RSHIFT: return Sdl_key::keyshift(); \
        case SDLK_LCTRL: \
        case SDLK_RCTRL: return Sdl_key::keyctrl(); \
        case SDLK_LALT: \
        case SDLK_RALT: return Sdl_key::keyalt(); \
        case SDLK_LGUI: \
        case SDLK_RGUI: return Sdl_key::keygui(); \
        case SDLK_COMMA: return Sdl_key::keycomma(); \
        case SDLK_PERIOD: return Sdl_key::keyperiod(); \
        case SDLK_SLASH: return Sdl_key::keyslash(); \
        case SDLK_SEMICOLON: return Sdl_key::keysemicolon(); \
        case SDLK_QUOTE: return Sdl_key::keyquote(); \
        case SDLK_LEFTBRACKET: return Sdl_key::keyleftbracket(); \
        case SDLK_RIGHTBRACKET: return Sdl_key::keyrightbracket(); \
        case SDLK_BACKSLASH: return Sdl_key::keybackslash(); \
        case SDLK_MINUS: return Sdl_key::keyminus(); \
        case SDLK_EQUALS: return Sdl_key::keyequals(); \
        case SDLK_BACKQUOTE: return Sdl_key::keybackquote(); \
        case SDLK_CAPSLOCK: return Sdl_key::keycapslock(); \
        case SDLK_NUMLOCKCLEAR: return Sdl_key::keynumlock(); \
        case SDLK_SCROLLLOCK: return Sdl_key::keyscrolllock(); \
        case SDLK_PRINTSCREEN: return Sdl_key::keyprintscreen(); \
        case SDLK_PAUSE: return Sdl_key::keypause(); \
        case SDLK_MENU: return Sdl_key::keymenu(); \
        case SDLK_F1: return Sdl_key::keyf1(); \
        case SDLK_F2: return Sdl_key::keyf2(); \
        case SDLK_F3: return Sdl_key::keyf3(); \
        case SDLK_F4: return Sdl_key::keyf4(); \
        case SDLK_F5: return Sdl_key::keyf5(); \
        case SDLK_F6: return Sdl_key::keyf6(); \
        case SDLK_F7: return Sdl_key::keyf7(); \
        case SDLK_F8: return Sdl_key::keyf8(); \
        case SDLK_F9: return Sdl_key::keyf9(); \
        case SDLK_F10: return Sdl_key::keyf10(); \
        case SDLK_F11: return Sdl_key::keyf11(); \
        case SDLK_F12: return Sdl_key::keyf12(); \
        case SDLK_0: return Sdl_key::keydigit0(); \
        case SDLK_1: return Sdl_key::keydigit1(); \
        case SDLK_2: return Sdl_key::keydigit2(); \
        case SDLK_3: return Sdl_key::keydigit3(); \
        case SDLK_4: return Sdl_key::keydigit4(); \
        case SDLK_5: return Sdl_key::keydigit5(); \
        case SDLK_6: return Sdl_key::keydigit6(); \
        case SDLK_7: return Sdl_key::keydigit7(); \
        case SDLK_8: return Sdl_key::keydigit8(); \
        case SDLK_9: return Sdl_key::keydigit9(); \
        case SDLK_a: return Sdl_key::keya(); \
        case SDLK_b: return Sdl_key::keyb(); \
        case SDLK_c: return Sdl_key::keyc(); \
        case SDLK_d: return Sdl_key::keyd(); \
        case SDLK_e: return Sdl_key::keye(); \
        case SDLK_f: return Sdl_key::keyf(); \
        case SDLK_g: return Sdl_key::keyg(); \
        case SDLK_h: return Sdl_key::keyh(); \
        case SDLK_i: return Sdl_key::keyi(); \
        case SDLK_j: return Sdl_key::keyj(); \
        case SDLK_k: return Sdl_key::keyk(); \
        case SDLK_l: return Sdl_key::keyl(); \
        case SDLK_m: return Sdl_key::keym(); \
        case SDLK_n: return Sdl_key::keyn(); \
        case SDLK_o: return Sdl_key::keyo(); \
        case SDLK_p: return Sdl_key::keyp(); \
        case SDLK_q: return Sdl_key::keyq(); \
        case SDLK_r: return Sdl_key::keyr(); \
        case SDLK_s: return Sdl_key::keys(); \
        case SDLK_t: return Sdl_key::keyt(); \
        case SDLK_u: return Sdl_key::keyu(); \
        case SDLK_v: return Sdl_key::keyv(); \
        case SDLK_w: return Sdl_key::keyw(); \
        case SDLK_x: return Sdl_key::keyx(); \
        case SDLK_y: return Sdl_key::keyy(); \
        case SDLK_z: return Sdl_key::keyz(); \
        case SDLK_UP: return Sdl_key::keyup(); \
        case SDLK_DOWN: return Sdl_key::keydown(); \
        case SDLK_LEFT: return Sdl_key::keyleft(); \
        case SDLK_RIGHT: return Sdl_key::keyright(); \
        default: return Sdl_key::keyother(code); \
        } \
      }; \
      auto decode_button = [&](const unsigned int code) -> std::shared_ptr<Sdl_mouse_button> { \
        switch (code) { \
        case SDL_BUTTON_LEFT: return Sdl_mouse_button::mouseleft(); \
        case SDL_BUTTON_MIDDLE: return Sdl_mouse_button::mousemiddle(); \
        case SDL_BUTTON_RIGHT: return Sdl_mouse_button::mouseright(); \
        case SDL_BUTTON_X1: return Sdl_mouse_button::mousex1(); \
        case SDL_BUTTON_X2: return Sdl_mouse_button::mousex2(); \
        default: return Sdl_mouse_button::mouseother(code); \
        } \
      }; \
      auto pos = std::make_pair(sdl_last_mouse_x(), sdl_last_mouse_y()); \
      switch (kind) { \
      case 0: return Sdl_event::eventnone(); \
      case 1: return Sdl_event::eventquit(); \
      case 2: return Sdl_event::eventkeydown(decode_key(keycode)); \
      case 3: return Sdl_event::eventkeyup(decode_key(keycode)); \
      case 4: return Sdl_event::eventmousemotion(pos); \
      case 5: return Sdl_event::eventmousebuttondown(decode_button(button), pos); \
      case 6: return Sdl_event::eventmousebuttonup(decode_button(button), pos); \
      default: return Sdl_event::eventnone(); \
      } \
    })()"
    "std::make_pair(sdl_last_mouse_x(), sdl_last_mouse_y())"
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

(** Extract the typed event poll smart constructor through the SDL helper decoder.

    This keeps [Rocqsweeper.v] on the smart-constructor interface even though
    Crane does not currently emit a reusable helper for this definition. *)
Crane Extract Inlined Constant sdl_poll_event =>
  "([&]() -> std::shared_ptr<Sdl_event> { \
      const unsigned int kind = sdl_poll_event_kind(); \
      const unsigned int keycode = sdl_last_key_code(); \
      const unsigned int button = sdl_last_mouse_button(); \
      auto decode_key = [&](const unsigned int code) -> std::shared_ptr<Sdl_key> { \
        switch (code) { \
        case SDLK_BACKSPACE: return Sdl_key::keybackspace(); \
        case SDLK_TAB: return Sdl_key::keytab(); \
        case SDLK_RETURN: return Sdl_key::keyreturn(); \
        case SDLK_ESCAPE: return Sdl_key::keyescape(); \
        case SDLK_SPACE: return Sdl_key::keyspace(); \
        case SDLK_INSERT: return Sdl_key::keyinsert(); \
        case SDLK_DELETE: return Sdl_key::keydelete(); \
        case SDLK_HOME: return Sdl_key::keyhome(); \
        case SDLK_END: return Sdl_key::keyend(); \
        case SDLK_PAGEUP: return Sdl_key::keypageup(); \
        case SDLK_PAGEDOWN: return Sdl_key::keypagedown(); \
        case SDLK_LSHIFT: \
        case SDLK_RSHIFT: return Sdl_key::keyshift(); \
        case SDLK_LCTRL: \
        case SDLK_RCTRL: return Sdl_key::keyctrl(); \
        case SDLK_LALT: \
        case SDLK_RALT: return Sdl_key::keyalt(); \
        case SDLK_LGUI: \
        case SDLK_RGUI: return Sdl_key::keygui(); \
        case SDLK_COMMA: return Sdl_key::keycomma(); \
        case SDLK_PERIOD: return Sdl_key::keyperiod(); \
        case SDLK_SLASH: return Sdl_key::keyslash(); \
        case SDLK_SEMICOLON: return Sdl_key::keysemicolon(); \
        case SDLK_QUOTE: return Sdl_key::keyquote(); \
        case SDLK_LEFTBRACKET: return Sdl_key::keyleftbracket(); \
        case SDLK_RIGHTBRACKET: return Sdl_key::keyrightbracket(); \
        case SDLK_BACKSLASH: return Sdl_key::keybackslash(); \
        case SDLK_MINUS: return Sdl_key::keyminus(); \
        case SDLK_EQUALS: return Sdl_key::keyequals(); \
        case SDLK_BACKQUOTE: return Sdl_key::keybackquote(); \
        case SDLK_CAPSLOCK: return Sdl_key::keycapslock(); \
        case SDLK_NUMLOCKCLEAR: return Sdl_key::keynumlock(); \
        case SDLK_SCROLLLOCK: return Sdl_key::keyscrolllock(); \
        case SDLK_PRINTSCREEN: return Sdl_key::keyprintscreen(); \
        case SDLK_PAUSE: return Sdl_key::keypause(); \
        case SDLK_MENU: return Sdl_key::keymenu(); \
        case SDLK_F1: return Sdl_key::keyf1(); \
        case SDLK_F2: return Sdl_key::keyf2(); \
        case SDLK_F3: return Sdl_key::keyf3(); \
        case SDLK_F4: return Sdl_key::keyf4(); \
        case SDLK_F5: return Sdl_key::keyf5(); \
        case SDLK_F6: return Sdl_key::keyf6(); \
        case SDLK_F7: return Sdl_key::keyf7(); \
        case SDLK_F8: return Sdl_key::keyf8(); \
        case SDLK_F9: return Sdl_key::keyf9(); \
        case SDLK_F10: return Sdl_key::keyf10(); \
        case SDLK_F11: return Sdl_key::keyf11(); \
        case SDLK_F12: return Sdl_key::keyf12(); \
        case SDLK_0: return Sdl_key::keydigit0(); \
        case SDLK_1: return Sdl_key::keydigit1(); \
        case SDLK_2: return Sdl_key::keydigit2(); \
        case SDLK_3: return Sdl_key::keydigit3(); \
        case SDLK_4: return Sdl_key::keydigit4(); \
        case SDLK_5: return Sdl_key::keydigit5(); \
        case SDLK_6: return Sdl_key::keydigit6(); \
        case SDLK_7: return Sdl_key::keydigit7(); \
        case SDLK_8: return Sdl_key::keydigit8(); \
        case SDLK_9: return Sdl_key::keydigit9(); \
        case SDLK_a: return Sdl_key::keya(); \
        case SDLK_b: return Sdl_key::keyb(); \
        case SDLK_c: return Sdl_key::keyc(); \
        case SDLK_d: return Sdl_key::keyd(); \
        case SDLK_e: return Sdl_key::keye(); \
        case SDLK_f: return Sdl_key::keyf(); \
        case SDLK_g: return Sdl_key::keyg(); \
        case SDLK_h: return Sdl_key::keyh(); \
        case SDLK_i: return Sdl_key::keyi(); \
        case SDLK_j: return Sdl_key::keyj(); \
        case SDLK_k: return Sdl_key::keyk(); \
        case SDLK_l: return Sdl_key::keyl(); \
        case SDLK_m: return Sdl_key::keym(); \
        case SDLK_n: return Sdl_key::keyn(); \
        case SDLK_o: return Sdl_key::keyo(); \
        case SDLK_p: return Sdl_key::keyp(); \
        case SDLK_q: return Sdl_key::keyq(); \
        case SDLK_r: return Sdl_key::keyr(); \
        case SDLK_s: return Sdl_key::keys(); \
        case SDLK_t: return Sdl_key::keyt(); \
        case SDLK_u: return Sdl_key::keyu(); \
        case SDLK_v: return Sdl_key::keyv(); \
        case SDLK_w: return Sdl_key::keyw(); \
        case SDLK_x: return Sdl_key::keyx(); \
        case SDLK_y: return Sdl_key::keyy(); \
        case SDLK_z: return Sdl_key::keyz(); \
        case SDLK_UP: return Sdl_key::keyup(); \
        case SDLK_DOWN: return Sdl_key::keydown(); \
        case SDLK_LEFT: return Sdl_key::keyleft(); \
        case SDLK_RIGHT: return Sdl_key::keyright(); \
        default: return Sdl_key::keyother(code); \
        } \
      }; \
      auto decode_button = [&](const unsigned int code) -> std::shared_ptr<Sdl_mouse_button> { \
        switch (code) { \
        case SDL_BUTTON_LEFT: return Sdl_mouse_button::mouseleft(); \
        case SDL_BUTTON_MIDDLE: return Sdl_mouse_button::mousemiddle(); \
        case SDL_BUTTON_RIGHT: return Sdl_mouse_button::mouseright(); \
        case SDL_BUTTON_X1: return Sdl_mouse_button::mousex1(); \
        case SDL_BUTTON_X2: return Sdl_mouse_button::mousex2(); \
        default: return Sdl_mouse_button::mouseother(code); \
        } \
      }; \
      auto pos = std::make_pair(sdl_last_mouse_x(), sdl_last_mouse_y()); \
      switch (kind) { \
      case 0: return Sdl_event::eventnone(); \
      case 1: return Sdl_event::eventquit(); \
      case 2: return Sdl_event::eventkeydown(decode_key(keycode)); \
      case 3: return Sdl_event::eventkeyup(decode_key(keycode)); \
      case 4: return Sdl_event::eventmousemotion(pos); \
      case 5: return Sdl_event::eventmousebuttondown(decode_button(button), pos); \
      case 6: return Sdl_event::eventmousebuttonup(decode_button(button), pos); \
      default: return Sdl_event::eventnone(); \
      } \
    })()" From "sdl_helpers.h".

(** Extract the mouse-position smart constructor to the helper pair value.

    This keeps the public Rocq API at the smart-constructor layer instead of
    exposing raw helper calls to the game implementation. *)
Crane Extract Inlined Constant sdl_get_mouse_position =>
  "std::make_pair(sdl_last_mouse_x(), sdl_last_mouse_y())" From "sdl_helpers.h".
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
