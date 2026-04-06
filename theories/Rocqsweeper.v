(** * Rocqsweeper game logic and rendering.

    The board model, mine placement, reveal/flag rules, rendering,
    and top-level SDL loop all live in Rocq and are extracted to C++
    through Crane. *)

From Corelib Require Import PrimString.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Bool.
From Stdlib Require Import Strings.String Strings.Ascii.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.Std Monads.ITree.
From Crane Require Extraction.
From CraneSDL2 Require Import SDL.

Local Open Scope pstring_scope.
Local Open Scope itree_scope.

(** Namespace containing the pure game logic, rendering, and extracted main loop. *)
Module Rocqsweeper.

Import ITreeNotations.


(** Board coordinates, stored as a row and column. *)
Record position : Type := mkPos { prow : nat; pcol : nat }.

(** The coarse game phase: still playing, won, or lost. *)
Inductive phase : Type := Playing | Won | Lost.

(** The per-cell game state: mine bit, reveal bit, flag bit, and adjacent-mine count. *)
Record tile : Type := mkTile {
  tile_mine : bool;
  tile_revealed : bool;
  tile_flagged : bool;
  tile_adjacent : nat
}.

(** The full pure game state carried through updates and rendering. *)
Record game_state : Type := mkState {
  board : list (list tile);
  cursor : position;
  game_phase : phase;
  waiting_for_first_reveal : bool;
  seed : nat
}.

(** Number of rows in the board. *)
Definition board_height : nat := 9.
(** Number of columns in the board. *)
Definition board_width : nat := 9.
(** Total number of cells in the board. *)
Definition total_cells : nat := board_height * board_width.
(** Number of mines to place in each generated board. *)
Definition mine_count : nat := 10.
(** Pixel size of one rendered cell. *)
Definition cell_size : nat := 42.
(** Pixel height reserved for the status and help text area. *)
Definition status_height : nat := 108.
(** Window width in pixels. *)
Definition win_width : nat := board_width * cell_size.
(** Window height in pixels. *)
Definition win_height : nat := board_height * cell_size + status_height.
(** Target frame delay in milliseconds. *)
Definition frame_ms : nat := 16.

(** The empty unrevealed unflagged tile used for initialization and defaults. *)
Definition blank_tile : tile := mkTile false false false 0.

(** Build a row filled with blank tiles. *)
Fixpoint repeat_tile (n : nat) : list tile :=
  match n with
  | 0 => []
  | S n' => blank_tile :: repeat_tile n'
  end.

(** Build a blank board with the requested number of rows. *)
Fixpoint repeat_board (h : nat) : list (list tile) :=
  match h with
  | 0 => []
  | S h' => repeat_tile board_width :: repeat_board h'
  end.

(** The initial blank board used before mine generation. *)
Definition blank_board : list (list tile) := repeat_board board_height.

(** Read a tile at a row and column, falling back to the blank tile out of bounds. *)
Definition get_tile (row col : nat) (b : list (list tile)) : tile :=
  nth col (nth row b []) blank_tile.

(** Replace one element of a list, leaving out-of-range updates unchanged. *)
Fixpoint replace_nth {A : Type} (n : nat) (xs : list A) (x : A) : list A :=
  match xs with
  | [] => []
  | y :: ys =>
    match n with
    | 0 => x :: ys
    | S n' => y :: replace_nth n' ys x
    end
  end.

(** Overwrite a tile at a row and column. *)
Definition set_tile (row col : nat) (t : tile) (b : list (list tile))
  : list (list tile) :=
  let r := nth row b [] in
  replace_nth row b (replace_nth col r t).

(** Overwrite a tile at a board position. *)
Definition set_tile_pos (p : position) (t : tile) (b : list (list tile))
  : list (list tile) :=
  set_tile (prow p) (pcol p) t b.

(** Read a tile at a board position. *)
Definition get_tile_pos (p : position) (b : list (list tile)) : tile :=
  get_tile (prow p) (pcol p) b.

(** Set the mine bit of a tile while keeping its other fields. *)
Definition tile_with_mine (t : tile) : tile :=
  mkTile true (tile_revealed t) (tile_flagged t) (tile_adjacent t).

(** Set the adjacent-mine count of a tile while keeping its other fields. *)
Definition tile_with_adjacent (t : tile) (n : nat) : tile :=
  mkTile (tile_mine t) (tile_revealed t) (tile_flagged t) n.

(** Reveal a tile and clear any flag on it. *)
Definition tile_reveal_clear_flag (t : tile) : tile :=
  mkTile (tile_mine t) true false (tile_adjacent t).

(** Toggle the flag bit of an unrevealed tile. *)
Definition tile_toggle_flag (t : tile) : tile :=
  mkTile (tile_mine t) false (negb (tile_flagged t)) (tile_adjacent t).

(** Boolean equality test on board positions. *)
Definition pos_eqb (p1 p2 : position) : bool :=
  Nat.eqb (prow p1) (prow p2) && Nat.eqb (pcol p1) (pcol p2).

(** Move the logical cursor vertically while clamping to the board. *)
Definition move_cursor_row (up : bool) (p : position) : position :=
  if up
  then mkPos (Nat.pred (prow p)) (pcol p)
  else mkPos (Nat.min (S (prow p)) (Nat.pred board_height)) (pcol p).

(** Move the logical cursor horizontally while clamping to the board. *)
Definition move_cursor_col (left : bool) (p : position) : position :=
  if left
  then mkPos (prow p) (Nat.pred (pcol p))
  else mkPos (prow p) (Nat.min (S (pcol p)) (Nat.pred board_width)).

(** Flatten a board position into a single linear index. *)
Definition board_index (p : position) : nat :=
  prow p * board_width + pcol p.

(** Recover the row from a linear board index. *)
Definition index_row (idx : nat) : nat := Nat.div idx board_width.
(** Recover the column from a linear board index. *)
Definition index_col (idx : nat) : nat := Nat.modulo idx board_width.
(** Recover a board position from a linear board index. *)
Definition index_pos (idx : nat) : position := mkPos (index_row idx) (index_col idx).

(** Count whether a given location contains a mine as 0 or 1. *)
Definition mine_at (row col : nat) (b : list (list tile)) : nat :=
  if tile_mine (get_tile row col b) then 1 else 0.

(** Test whether a cell has an upward neighbor. *)
Definition has_up (r : nat) : bool := negb (Nat.eqb r 0).
(** Test whether a cell has a left neighbor. *)
Definition has_left (c : nat) : bool := negb (Nat.eqb c 0).
(** Test whether a cell has a downward neighbor. *)
Definition has_down (r : nat) : bool := Nat.ltb (S r) board_height.
(** Test whether a cell has a right neighbor. *)
Definition has_right (c : nat) : bool := Nat.ltb (S c) board_width.

(** Count the mines in the eight-neighbor hood around a cell. *)
Definition adjacent_mines (row col : nat) (b : list (list tile)) : nat :=
  let up := has_up row in
  let left := has_left col in
  let down := has_down row in
  let right := has_right col in
  (if up && left then mine_at (Nat.pred row) (Nat.pred col) b else 0) +
  (if up then mine_at (Nat.pred row) col b else 0) +
  (if up && right then mine_at (Nat.pred row) (S col) b else 0) +
  (if left then mine_at row (Nat.pred col) b else 0) +
  (if right then mine_at row (S col) b else 0) +
  (if down && left then mine_at (S row) (Nat.pred col) b else 0) +
  (if down then mine_at (S row) col b else 0) +
  (if down && right then mine_at (S row) (S col) b else 0).

(** Fill the adjacent-mine counts for one row. *)
Fixpoint annotate_row (row col : nat) (cells : list tile) (b : list (list tile))
  : list tile :=
  match cells with
  | [] => []
  | t :: rest =>
    tile_with_adjacent t (adjacent_mines row col b) ::
    annotate_row row (S col) rest b
  end.

(** Fill adjacent-mine counts for every row in the board. *)
Fixpoint annotate_board_rows (row : nat) (rows b : list (list tile))
  : list (list tile) :=
  match rows with
  | [] => []
  | cells :: rest =>
    annotate_row row 0 cells b :: annotate_board_rows (S row) rest b
  end.

(** Compute the visible adjacent-mine counts for a mined board. *)
Definition annotate_board (b : list (list tile)) : list (list tile) :=
  annotate_board_rows 0 b b.

(** Advance the pseudo-random seed used for mine placement. *)
Definition next_seed (s : nat) : nat :=
  Nat.modulo (s * 73 + 41) 104729.

(** Place mines recursively while skipping the designated safe cell and duplicates. *)
Fixpoint place_mines (fuel mines_left cur_seed safe_idx : nat)
    (b : list (list tile)) : list (list tile) :=
  match fuel with
  | 0 => b
  | S fuel' =>
    match mines_left with
    | 0 => b
    | S mines_left' =>
      let idx := Nat.modulo cur_seed total_cells in
      let p := index_pos idx in
      let t := get_tile_pos p b in
      if Nat.eqb idx safe_idx || tile_mine t
      then place_mines fuel' mines_left (next_seed cur_seed) safe_idx b
      else
        place_mines fuel' mines_left' (next_seed cur_seed) safe_idx
                    (set_tile_pos p (tile_with_mine t) b)
    end
  end.

(** Generate a first-click-safe mined board and annotate it. *)
Definition generate_board (seed0 : nat) (safe : position) : list (list tile) :=
  annotate_board (place_mines (total_cells * 6) mine_count seed0 (board_index safe) blank_board).

(** Prepend a position to a worklist when a guard holds. *)
Definition append_if (cond : bool) (p : position) (rest : list position)
  : list position :=
  if cond then p :: rest else rest.

(** Enumerate the valid neighboring positions of a cell. *)
Definition neighbors (p : position) : list position :=
  let r := prow p in
  let c := pcol p in
  let up := has_up r in
  let left := has_left c in
  let down := has_down r in
  let right := has_right c in
  append_if (down && right) (mkPos (S r) (S c))
    (append_if down (mkPos (S r) c)
      (append_if (down && left) (mkPos (S r) (Nat.pred c))
        (append_if right (mkPos r (S c))
          (append_if left (mkPos r (Nat.pred c))
            (append_if (up && right) (mkPos (Nat.pred r) (S c))
              (append_if up (mkPos (Nat.pred r) c)
                (append_if (up && left) (mkPos (Nat.pred r) (Nat.pred c)) []))))))).

(** Reveal a worklist of cells, expanding through zero-adjacent cells. *)
Fixpoint reveal_region (fuel : nat) (todo : list position) (b : list (list tile))
  : list (list tile) :=
  match fuel with
  | 0 => b
  | S fuel' =>
    match todo with
    | [] => b
    | p :: rest =>
      let t := get_tile_pos p b in
      if tile_revealed t || tile_flagged t || tile_mine t
      then reveal_region fuel' rest b
      else
        let b1 := set_tile_pos p (tile_reveal_clear_flag t) b in
        let todo' := if Nat.eqb (tile_adjacent t) 0 then neighbors p ++ rest else rest in
        reveal_region fuel' todo' b1
    end
  end.

(** Count hidden non-mine cells in one row. *)
Fixpoint hidden_safe_in_row (cells : list tile) : nat :=
  match cells with
  | [] => 0
  | t :: rest =>
    (if tile_mine t || tile_revealed t then 0 else 1) + hidden_safe_in_row rest
  end.

(** Count hidden non-mine cells in the whole board. *)
Fixpoint hidden_safe_total (rows : list (list tile)) : nat :=
  match rows with
  | [] => 0
  | row :: rest => hidden_safe_in_row row + hidden_safe_total rest
  end.

(** Count flagged cells in one row. *)
Fixpoint flagged_in_row (cells : list tile) : nat :=
  match cells with
  | [] => 0
  | t :: rest => (if tile_flagged t then 1 else 0) + flagged_in_row rest
  end.

(** Count flagged cells in the whole board. *)
Fixpoint flagged_total (rows : list (list tile)) : nat :=
  match rows with
  | [] => 0
  | row :: rest => flagged_in_row row + flagged_total rest
  end.

(** Compute the displayed mines-left counter from placed flags. *)
Definition mines_left_display (gs : game_state) : nat :=
  mine_count - flagged_total (board gs).

(** Rebuild a game state after a board update, refreshing derived phase fields. *)
Definition state_with_board (gs : game_state) (b : list (list tile)) : game_state :=
  let ph :=
    if Nat.eqb (hidden_safe_total b) 0 then Won
    else game_phase gs in
  mkState b (cursor gs) ph false (seed gs).

(** The tile examined by the playing-phase reveal logic on a chosen source board. *)
Definition reveal_playing_source_tile (gs : game_state) (board0 : list (list tile)) : tile :=
  get_tile_pos (cursor gs) board0.

(** The board produced by the playing-phase reveal logic on a chosen source board. *)
Definition reveal_playing_result_board (gs : game_state) (board0 : list (list tile))
  : list (list tile) :=
  let cur := cursor gs in
  let tile0 := reveal_playing_source_tile gs board0 in
  if tile_flagged tile0 || tile_revealed tile0 then
    board0
  else if tile_mine tile0 then
    set_tile_pos cur (tile_reveal_clear_flag tile0) board0
  else
    reveal_region (total_cells * total_cells) [cur] board0.

(** The phase produced by the playing-phase reveal logic on a chosen source board. *)
Definition reveal_playing_result_phase (gs : game_state) (board0 : list (list tile)) : phase :=
  let tile0 := reveal_playing_source_tile gs board0 in
  if tile_flagged tile0 || tile_revealed tile0 then
    Playing
  else if tile_mine tile0 then
    Lost
  else if Nat.eqb (hidden_safe_total (reveal_playing_result_board gs board0)) 0 then Won else Playing.

(** The playing-phase reveal logic parameterized by the board it starts from. *)
Definition reveal_playing_from_board (gs : game_state) (board0 : list (list tile)) : game_state :=
  mkState (reveal_playing_result_board gs board0)
          (cursor gs)
          (reveal_playing_result_phase gs board0)
          false
          (seed gs).

(** Apply the reveal action at the current cursor position. *)
Definition reveal_at_cursor (gs : game_state) : game_state :=
  match game_phase gs with
  | Won => gs
  | Lost => gs
  | Playing =>
    let cur := cursor gs in
    let board0 :=
      if waiting_for_first_reveal gs
      then generate_board (seed gs) cur
      else board gs in
    reveal_playing_from_board gs board0
  end.

(** Apply the flag-toggle action at the current cursor position. *)
Definition toggle_flag_at_cursor (gs : game_state) : game_state :=
  match game_phase gs with
  | Playing =>
    let t := get_tile_pos (cursor gs) (board gs) in
    if tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)
    then gs
    else
      mkState (set_tile_pos (cursor gs) (tile_toggle_flag t) (board gs))
              (cursor gs) Playing (waiting_for_first_reveal gs) (seed gs)
  | _ => gs
  end.

(** Create a fresh initial game state from a seed. *)
Definition initial_state (seed0 : nat) : game_state :=
  mkState blank_board (mkPos 0 0) Playing true seed0.

(** Restart the game with a derived next seed. *)
Definition restart_state (gs : game_state) : game_state :=
  initial_state (next_seed (seed gs)).

(** Update only the cursor field of the game state. *)
Definition set_cursor (p : position) (gs : game_state) : game_state :=
  mkState (board gs) p (game_phase gs) (waiting_for_first_reveal gs) (seed gs).

(** Update the cursor by applying a function to the current cursor position. *)
Definition map_cursor (f : position -> position) (gs : game_state) : game_state :=
  set_cursor (f (cursor gs)) gs.

(** Pixel height of the playable grid without the status bar. *)
Definition board_pixel_height : nat := board_height * cell_size.

(** Map a mouse position to a board position when the pointer is inside the grid. *)
Definition mouse_board_pos (mp : nat * nat) : option position :=
  let '(mx, my) := mp in
  if Nat.ltb mx win_width && Nat.ltb my board_pixel_height
  then Some (mkPos (Nat.div my cell_size) (Nat.div mx cell_size))
  else None.

(** Apply a position-based state update when the mouse is over a board cell. *)
Definition with_mouse_board_pos
    (f : position -> game_state -> game_state) (mp : nat * nat) (gs : game_state)
  : game_state :=
  match mouse_board_pos mp with
  | Some p => f p gs
  | None => gs
  end.

(** Interpret a mouse click as a reveal action when it hits the board. *)
Definition mouse_reveal (mp : nat * nat) (gs : game_state) : game_state :=
  with_mouse_board_pos (fun p gs0 => reveal_at_cursor (set_cursor p gs0)) mp gs.

(** Interpret a mouse click as a flag action when it hits the board. *)
Definition mouse_flag (mp : nat * nat) (gs : game_state) : game_state :=
  with_mouse_board_pos (fun p gs0 => toggle_flag_at_cursor (set_cursor p gs0)) mp gs.

(** Move the logical cursor to the hovered cell when the mouse is on the board. *)
Definition sync_cursor_with_mouse (mp : nat * nat) (gs : game_state) : game_state :=
  with_mouse_board_pos set_cursor mp gs.

(** Move the cursor in response to a directional key press. *)
Definition handle_direction_key (key : sdl_key) (gs : game_state) : game_state :=
  match key with
  | KeyUp | KeyW => map_cursor (move_cursor_row true) gs
  | KeyDown | KeyS => map_cursor (move_cursor_row false) gs
  | KeyLeft | KeyA => map_cursor (move_cursor_col true) gs
  | KeyRight | KeyD => map_cursor (move_cursor_col false) gs
  | _ => gs
  end.

(** Translate a key press into a quit flag and next pure state. *)
Definition handle_key_down (key : sdl_key) (gs : game_state) : bool * game_state :=
  match key with
  | KeyEscape | KeyQ => (true, gs)
  | KeySpace => (false, reveal_at_cursor gs)
  | KeyF => (false, toggle_flag_at_cursor gs)
  | KeyR => (false, restart_state gs)
  | _ => (false, handle_direction_key key gs)
  end.

(** Translate a mouse-button press into a quit flag and next pure state. *)
Definition handle_mouse_button_down (button : sdl_mouse_button)
    (mp : nat * nat) (gs : game_state) : bool * game_state :=
  match button with
  | MouseLeft => (false, mouse_reveal mp gs)
  | MouseRight => (false, mouse_flag mp gs)
  | _ => (false, gs)
  end.

(** Translate a generic SDL event into a quit flag and next pure state. *)
Definition handle_event (ev : sdl_event) (gs : game_state) : bool * game_state :=
  match ev with
  | EventNone => (false, gs)
  | EventQuit => (true, gs)
  | EventKeyDown key => handle_key_down key gs
  | EventKeyUp _ => (false, gs)
  | EventMouseMotion mp => (false, sync_cursor_with_mouse mp gs)
  | EventMouseButtonDown button mp => handle_mouse_button_down button mp gs
  | EventMouseButtonUp _ _ => (false, gs)
  end.

(** Left pixel coordinate of a column. *)
Definition cell_left (col : nat) : nat := col * cell_size.
(** Top pixel coordinate of a row. *)
Definition cell_top (row : nat) : nat := row * cell_size.
(** Inset used for interior cell drawing. *)
Definition inset : nat := 4.

(** Return one bitmap row of one font glyph. *)
Definition glyph_row_data (g row : nat) : nat :=
  nth row (nth g
    [ [14;17;19;21;25;17;14]
    ; [4;12;4;4;4;4;14]
    ; [14;17;1;6;8;16;31]
    ; [14;17;1;6;1;17;14]
    ; [2;6;10;18;31;2;2]
    ; [31;16;30;1;1;17;14]
    ; [6;8;16;30;17;17;14]
    ; [31;1;2;4;8;8;8]
    ; [14;17;17;14;17;17;14]
    ; [14;17;17;15;1;2;12]
    ; [0;0;0;0;0;0;0]
    ; [4;10;17;17;31;17;17]
    ; [30;17;17;30;17;17;30]
    ; [14;17;16;16;16;17;14]
    ; [28;18;17;17;17;18;28]
    ; [31;16;16;30;16;16;31]
    ; [31;16;16;30;16;16;16]
    ; [14;17;16;23;17;17;14]
    ; [17;17;17;31;17;17;17]
    ; [14;4;4;4;4;4;14]
    ; [7;2;2;2;2;18;12]
    ; [17;18;20;24;20;18;17]
    ; [16;16;16;16;16;16;31]
    ; [17;27;21;17;17;17;17]
    ; [17;25;21;19;17;17;17]
    ; [14;17;17;17;17;17;14]
    ; [30;17;17;30;16;16;16]
    ; [14;17;17;17;21;18;13]
    ; [30;17;17;30;20;18;17]
    ; [14;17;16;14;1;17;14]
    ; [31;4;4;4;4;4;4]
    ; [17;17;17;17;17;17;14]
    ; [17;17;17;17;10;10;4]
    ; [17;17;17;21;21;21;10]
    ; [17;17;10;4;10;17;17]
    ; [17;17;10;4;4;4;4]
    ; [31;1;2;4;8;16;31]
    ; [0;4;4;0;4;4;0]
    ; [1;2;4;8;16;0;0]
    ; [0;0;14;1;15;17;15]
    ; [16;16;22;25;17;17;30]
    ; [0;0;14;16;16;17;14]
    ; [1;1;13;19;17;17;15]
    ; [0;0;14;17;31;16;14]
    ; [6;8;30;8;8;8;8]
    ; [0;0;15;17;15;1;14]
    ; [16;16;22;25;17;17;17]
    ; [4;0;12;4;4;4;14]
    ; [2;0;6;2;2;18;12]
    ; [16;16;18;20;24;20;18]
    ; [12;4;4;4;4;4;14]
    ; [0;0;26;21;21;21;21]
    ; [0;0;22;25;17;17;17]
    ; [0;0;14;17;17;17;14]
    ; [0;0;30;17;30;16;16]
    ; [0;0;13;19;15;1;1]
    ; [0;0;22;25;16;16;16]
    ; [0;0;15;16;14;1;30]
    ; [8;8;30;8;8;9;6]
    ; [0;0;17;17;17;19;13]
    ; [0;0;17;17;17;10;4]
    ; [0;0;17;17;21;21;10]
    ; [0;0;17;10;4;10;17]
    ; [0;0;17;17;15;1;14]
    ; [0;0;31;2;4;8;31]
    ] []) 0.

(** Draw one row of one bitmap glyph. *)
Fixpoint draw_glyph_row (ren : sdl_renderer) (sx sy row_bits dx count scale : nat)
  : itree sdlE void :=
  match count with
  | 0 => Ret ghost
  | S count' =>
    (if Nat.testbit row_bits (4 - dx)
     then sdl_fill_rect ren (sx + dx * scale) sy scale scale
     else Ret ghost) ;;
    draw_glyph_row ren sx sy row_bits (S dx) count' scale
  end.

(** Draw all bitmap rows of one glyph. *)
Fixpoint draw_glyph_rows (ren : sdl_renderer) (sx sy g row count scale : nat)
  : itree sdlE void :=
  match count with
  | 0 => Ret ghost
  | S count' =>
    draw_glyph_row ren sx (sy + row * scale) (glyph_row_data g row) 0 5 scale ;;
    draw_glyph_rows ren sx sy g (S row) count' scale
  end.

(** Draw a single glyph at a given location. *)
Definition draw_one_glyph (ren : sdl_renderer) (sx sy g scale : nat) : itree sdlE void :=
  draw_glyph_rows ren sx sy g 0 7 scale.

(** Map an ASCII character to the corresponding bitmap glyph id. *)
Definition ascii_to_glyph (a : ascii) : nat :=
  let n := nat_of_ascii a in
  if Nat.leb 48 n && Nat.leb n 57 then n - 48
  else if Nat.eqb n 32 then 10
  else if Nat.leb 65 n && Nat.leb n 90 then 11 + (n - 65)
  else if Nat.eqb n 58 then 37
  else if Nat.eqb n 47 then 38
  else if Nat.leb 97 n && Nat.leb n 122 then 39 + (n - 97)
  else 10.

(** Convert a Rocq string into glyph ids for the bitmap font. *)
Fixpoint string_to_glyphs (s : String.string) : list nat :=
  match s with
  | EmptyString => []
  | String a rest => ascii_to_glyph a :: string_to_glyphs rest
  end.

(** Draw a list of glyph ids in a row. *)
Fixpoint draw_glyphs (ren : sdl_renderer) (sx sy scale : nat) (glyphs : list nat)
  : itree sdlE void :=
  match glyphs with
  | [] => Ret ghost
  | g :: rest =>
    draw_one_glyph ren sx sy g scale ;;
    draw_glyphs ren (sx + 6 * scale) sy scale rest
  end.

(** Draw the decimal digits of a natural number recursively. *)
Fixpoint draw_number_digits (ren : sdl_renderer) (sx sy scale : nat)
    (digits : list nat) : itree sdlE void :=
  match digits with
  | [] => Ret ghost
  | d :: rest =>
    draw_one_glyph ren sx sy d scale ;;
    draw_number_digits ren (sx + 6 * scale) sy scale rest
  end.

(** Draw a natural number using the bitmap font. *)
Definition draw_number (ren : sdl_renderer) (n sx sy scale : nat) : itree sdlE void :=
  draw_number_digits ren sx sy scale (nat_digit_list n).

(** Draw a Rocq string using the bitmap font. *)
Definition draw_text (ren : sdl_renderer) (sx sy scale : nat) (msg : String.string)
  : itree sdlE void :=
  draw_glyphs ren sx sy scale (string_to_glyphs msg).

(** Draw the colored numeral for a revealed numbered cell. *)
Definition draw_cell_number (ren : sdl_renderer) (n x y : nat) : itree sdlE void :=
  let '(r, g, b) :=
    match n with
    | 1 => (40, 80, 210)
    | 2 => (30, 145, 70)
    | 3 => (200, 40, 40)
    | 4 => (80, 40, 150)
    | 5 => (150, 40, 40)
    | 6 => (30, 130, 140)
    | 7 => (30, 30, 30)
    | _ => (120, 50, 20)
    end in
  sdl_set_draw_color ren r g b ;;
  draw_one_glyph ren x y n 2.

(** Draw the flag icon for a flagged cell. *)
Definition draw_flag (ren : sdl_renderer) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 60 60 60 ;;
  sdl_fill_rect ren (x + 15) (y + 8) 3 24 ;;
  sdl_set_draw_color ren 220 60 60 ;;
  sdl_fill_rect ren (x + 10) (y + 8) 12 3 ;;
  sdl_fill_rect ren (x + 10) (y + 11) 9 3 ;;
  sdl_fill_rect ren (x + 10) (y + 14) 6 3.

(** Draw the mine icon for a mined cell. *)
Definition draw_mine (ren : sdl_renderer) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 30 30 30 ;;
  sdl_fill_rect ren (x + 12) (y + 12) 14 14 ;;
  sdl_fill_rect ren (x + 5) (y + 17) 28 4 ;;
  sdl_fill_rect ren (x + 17) (y + 5) 4 28 ;;
  sdl_set_draw_color ren 230 230 230 ;;
  sdl_fill_rect ren (x + 14) (y + 14) 4 4.

(** Draw the background of a hidden cell. *)
Definition draw_hidden_tile (ren : sdl_renderer) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 132 151 173 ;;
  sdl_fill_rect ren x y cell_size cell_size ;;
  sdl_set_draw_color ren 176 190 205 ;;
  sdl_fill_rect ren x y cell_size 5 ;;
  sdl_fill_rect ren x y 5 cell_size ;;
  sdl_set_draw_color ren 93 113 137 ;;
  sdl_fill_rect ren x (y + cell_size - 5) cell_size 5 ;;
  sdl_fill_rect ren (x + cell_size - 5) y 5 cell_size.

(** Draw the background of a revealed cell. *)
Definition draw_revealed_tile (ren : sdl_renderer) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 222 226 230 ;;
  sdl_fill_rect ren x y cell_size cell_size ;;
  sdl_set_draw_color ren 190 195 199 ;;
  sdl_fill_rect ren x y cell_size 1 ;;
  sdl_fill_rect ren x y 1 cell_size.

(** Draw the yellow selection frame around the current cursor cell. *)
Definition draw_cursor (ren : sdl_renderer) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 255 215 0 ;;
  sdl_fill_rect ren x y cell_size 3 ;;
  sdl_fill_rect ren x y 3 cell_size ;;
  sdl_fill_rect ren x (y + cell_size - 3) cell_size 3 ;;
  sdl_fill_rect ren (x + cell_size - 3) y 3 cell_size.

(** Draw the visible contents of one tile. *)
Definition draw_tile_contents (ren : sdl_renderer) (x y : nat) (t : tile) (show_mines : bool)
  : itree sdlE void :=
  if tile_revealed t then
    if tile_mine t then draw_mine ren x y
    else if Nat.eqb (tile_adjacent t) 0 then Ret ghost
         else draw_cell_number ren (tile_adjacent t) (x + 16) (y + 13)
  else if tile_flagged t then
    draw_flag ren x y
  else if show_mines && tile_mine t then
    draw_mine ren x y
  else Ret ghost.

(** Draw one board row. *)
Fixpoint draw_row (ren : sdl_renderer) (row col : nat) (cells : list tile)
    (cur : position) (show_mines : bool) : itree sdlE void :=
  match cells with
  | [] => Ret ghost
  | t :: rest =>
    let x := cell_left col in
    let y := cell_top row in
    (if tile_revealed t then draw_revealed_tile ren x y else draw_hidden_tile ren x y) ;;
    draw_tile_contents ren x y t show_mines ;;
    (if pos_eqb cur (mkPos row col) then draw_cursor ren x y else Ret ghost) ;;
    draw_row ren row (S col) rest cur show_mines
  end.

(** Draw the whole board row by row. *)
Fixpoint draw_rows (ren : sdl_renderer) (row : nat) (rows : list (list tile))
    (cur : position) (show_mines : bool) : itree sdlE void :=
  match rows with
  | [] => Ret ghost
  | cells :: rest =>
    draw_row ren row 0 cells cur show_mines ;;
    draw_rows ren (S row) rest cur show_mines
  end.

(** Status label for the mine counter. *)
Definition msg_mines : String.string := "MINES"%string.
(** Status label for the remaining-safe-cells counter. *)
Definition msg_left : String.string := "LEFT"%string.
(** Status banner shown after a win. *)
Definition msg_won : String.string := "YOU WON"%string.
(** Status banner shown after a loss. *)
Definition msg_lost : String.string := "LOST"%string.
(** Help text explaining the reveal controls. *)
Definition msg_reveal_hint : String.string := "Reveal: Space or left click"%string.
(** Help text explaining the flag controls. *)
Definition msg_flag_hint : String.string := "Flag: F or right click"%string.
(** Help text explaining restart and exit controls. *)
Definition msg_restart_exit_hint : String.string := "Restart: R   Exit: Esc"%string.

(** Draw a text label followed by a numeric value. *)
Definition draw_label_number (ren : sdl_renderer) (label : String.string) (n x y : nat)
  : itree sdlE void :=
  sdl_set_draw_color ren 20 35 50 ;;
  draw_text ren x y 2 label ;;
  draw_number ren n (x + 78) y 2.

(** Draw one line of status text. *)
Definition draw_status_text (ren : sdl_renderer) (msg : String.string) (x y : nat) : itree sdlE void :=
  sdl_set_draw_color ren 20 35 50 ;;
  draw_text ren x y 2 msg.

(** Draw the counters, outcome banner, and controls help. *)
Definition draw_status_bar (ren : sdl_renderer) (gs : game_state) : itree sdlE void :=
  let top := board_height * cell_size in
  sdl_set_draw_color ren 208 214 221 ;;
  sdl_fill_rect ren 0 top win_width status_height ;;
  draw_label_number ren msg_mines (mines_left_display gs) 12 (top + 12) ;;
  sdl_set_draw_color ren 20 35 50 ;;
  draw_text ren 12 (top + 40) 2 msg_reveal_hint ;;
  draw_text ren 12 (top + 60) 2 msg_flag_hint ;;
  draw_text ren 12 (top + 80) 2 msg_restart_exit_hint ;;
  match game_phase gs with
  | Playing => Ret ghost
  | Won => draw_status_text ren msg_won 270 (top + 12)
  | Lost => draw_status_text ren msg_lost 282 (top + 12)
  end.

(** Render one complete frame for the current game state. *)
Definition render_frame (ren : sdl_renderer) (gs : game_state) : itree sdlE void :=
  sdl_set_draw_color ren 245 246 247 ;;
  sdl_clear ren ;;
  draw_rows ren 0 (board gs) (cursor gs)
            (match game_phase gs with Lost => true | _ => false end) ;;
  draw_status_bar ren gs ;;
  sdl_present ren.

(** Mutable loop state used by the extracted SDL game loop. *)
Record loop_state : Type := mkLoop {
  ls_game : game_state;
  ls_started : nat
}.

(** Sleep long enough to respect the target frame time. *)
Definition frame_delay (frame_start : nat) : itree sdlE void :=
  now2 <- sdl_get_ticks ;;
  let elapsed := now2 - frame_start in
  if Nat.ltb elapsed frame_ms
  then sdl_delay (frame_ms - elapsed)
  else Ret ghost.

(** Path to the sound played after revealing a mine. *)
Definition snd_mine : PrimString.string := "assets/mine.mp3".
(** Path to the sound played after revealing a safe cell. *)
Definition snd_tap : PrimString.string := "assets/tap.mp3".
(** Path to the sound played after winning. *)
Definition snd_win : PrimString.string := "assets/win.mp3".

(** Boolean equality test on game phases. *)
Definition phase_eqb (p1 p2 : phase) : bool :=
  match p1, p2 with
  | Playing, Playing => true
  | Won, Won => true
  | Lost, Lost => true
  | _, _ => false
  end.

(** Recognize the input events that should trigger reveal sounds. *)
Definition is_reveal_event (ev : sdl_event) : bool :=
  match ev with
  | EventKeyDown KeySpace => true
  | EventMouseButtonDown MouseLeft _ => true
  | _ => false
  end.

(** Choose and play the appropriate reveal-related sound effect. *)
Definition maybe_play_sound (ev : sdl_event) (before after : game_state) : itree sdlE void :=
  if negb (is_reveal_event ev) then Ret ghost
  else if negb (phase_eqb (game_phase before) Won) && phase_eqb (game_phase after) Won
       then sdl_play_sound snd_win
       else if negb (phase_eqb (game_phase before) Lost) && phase_eqb (game_phase after) Lost
            then sdl_play_sound snd_mine
            else if Nat.ltb (hidden_safe_total (board after))
                             (hidden_safe_total (board before))
                 then sdl_play_sound snd_tap
                 else Ret ghost.

(** Process one input frame and produce the next loop state. *)
Definition process_frame (ren : sdl_renderer) (ls : loop_state)
  : itree sdlE (bool * loop_state) :=
  frame_start <- sdl_get_ticks ;;
  ev <- sdl_poll_event ;;
  mp <- sdl_get_mouse_position ;;
  let gs0 := sync_cursor_with_mouse mp (ls_game ls) in
  let '(quit, gs1) := handle_event ev gs0 in
  maybe_play_sound ev gs0 gs1 ;;
  let ls1 := mkLoop gs1 (ls_started ls) in
  render_frame ren (ls_game ls1) ;;
  frame_delay frame_start ;;
  Ret (quit, ls1).

(** Initialize SDL resources and the initial loop state. *)
Definition init_game : itree sdlE (sdl_window * sdl_renderer * loop_state) :=
  win <- sdl_create_window "Rocqsweeper" win_width win_height ;;
  ren <- sdl_create_renderer win ;;
  t0 <- sdl_get_ticks ;;
  let gs := initial_state t0 in
  render_frame ren gs ;;
  Ret (win, ren, mkLoop gs t0).

(** Release SDL resources before exiting. *)
Definition cleanup (ren : sdl_renderer) (win : sdl_window) : itree sdlE void :=
  sdl_destroy ren win.

End Rocqsweeper.

Import Rocqsweeper.
Import ITreeNotations.

Axiom c_int : Type.
Axiom c_zero : c_int.

(** Cleanup wrapper returning a C integer exit code. *)
Definition exit_game (win : sdl_window) (ren : sdl_renderer) : itree sdlE c_int :=
  cleanup ren win ;;
  Ret c_zero.

(** Main corecursive SDL game loop. *)
CoFixpoint run_game (win : sdl_window) (ren : sdl_renderer)
                    (ls : loop_state) : itree sdlE c_int :=
  res <- process_frame ren ls ;;
  let '(quit, ls') := res in
  if quit then exit_game win ren else Tau (run_game win ren ls').

(** Program entry point used by extraction. *)
Definition main : itree sdlE c_int :=
  init <- init_game ;;
  let '(win_ren, ls) := init in
  let '(win, ren) := win_ren in
  run_game win ren ls.

Crane Extract Inlined Constant c_int => "int".
Crane Extract Inlined Constant c_zero => "0".

Crane Extraction "rocqsweeper" Rocqsweeper main.
