From Stdlib Require Import Lia Bool PeanoNat.
From RocqsweeperGame Require Import Rocqsweeper GameProofs.

Import Rocqsweeper.

(** * Cursor and input-mapping layer *)

Inductive pure_interaction_step : game_state -> game_state -> Prop :=
| PureInteractionSetCursor : forall p gs,
    pure_interaction_step gs (set_cursor p gs)
| PureInteractionSyncCursor : forall mx my gs,
    pure_interaction_step gs (sync_cursor_with_mouse mx my gs)
| PureInteractionMouseReveal : forall mx my gs,
    pure_interaction_step gs (mouse_reveal mx my gs)
| PureInteractionMouseFlag : forall mx my gs,
    pure_interaction_step gs (mouse_flag mx my gs).

(** Changing the cursor leaves the board itself unchanged. *)
Lemma set_cursor_board :
  forall p gs, board (set_cursor p gs) = board gs.
Proof.
  reflexivity.
Qed.

(** Changing the cursor leaves the game phase unchanged. *)
Lemma set_cursor_phase :
  forall p gs, game_phase (set_cursor p gs) = game_phase gs.
Proof.
  reflexivity.
Qed.

(** Changing the cursor leaves the first-reveal flag unchanged. *)
Lemma set_cursor_waiting :
  forall p gs,
    waiting_for_first_reveal (set_cursor p gs) = waiting_for_first_reveal gs.
Proof.
  reflexivity.
Qed.

(** Changing the cursor does not affect the hidden-safe-cell count. *)
Lemma set_cursor_hidden_safe_total :
  forall p gs,
    hidden_safe_total (board (set_cursor p gs)) = hidden_safe_total (board gs).
Proof.
  intros. rewrite set_cursor_board. reflexivity.
Qed.

(** Changing the cursor does not affect the flag count. *)
Lemma set_cursor_flagged_total :
  forall p gs,
    flagged_total (board (set_cursor p gs)) = flagged_total (board gs).
Proof.
  intros. rewrite set_cursor_board. reflexivity.
Qed.

(** Mouse synchronization is a no-op when the mouse is outside the board. *)
Lemma sync_cursor_with_mouse_outside :
  forall mx my gs,
    mouse_board_pos mx my = None ->
    sync_cursor_with_mouse mx my gs = gs.
Proof.
  intros mx my gs Hmouse.
  unfold sync_cursor_with_mouse.
  rewrite Hmouse.
  reflexivity.
Qed.

(** Mouse synchronization sets the cursor to the hovered board cell. *)
Lemma sync_cursor_with_mouse_inside :
  forall mx my p gs,
    mouse_board_pos mx my = Some p ->
    sync_cursor_with_mouse mx my gs = set_cursor p gs.
Proof.
  intros mx my p gs Hmouse.
  unfold sync_cursor_with_mouse.
  rewrite Hmouse.
  reflexivity.
Qed.

(** Mouse synchronization does not change the hidden-safe-cell count. *)
Lemma sync_cursor_with_mouse_hidden_safe_total :
  forall mx my gs,
    hidden_safe_total (board (sync_cursor_with_mouse mx my gs)) =
    hidden_safe_total (board gs).
Proof.
  intros mx my gs.
  unfold sync_cursor_with_mouse.
  destruct (mouse_board_pos mx my); simpl; reflexivity.
Qed.

(** Mouse synchronization does not change the flag count. *)
Lemma sync_cursor_with_mouse_flagged_total :
  forall mx my gs,
    flagged_total (board (sync_cursor_with_mouse mx my gs)) =
    flagged_total (board gs).
Proof.
  intros mx my gs.
  unfold sync_cursor_with_mouse.
  destruct (mouse_board_pos mx my); simpl; reflexivity.
Qed.

(** Predicate saying that the current cursor lies inside the board. *)
Definition cursor_in_bounds (gs : game_state) : Prop :=
  prow (cursor gs) < board_height /\ pcol (cursor gs) < board_width.

(** Vertical cursor movement stays within the board bounds. *)
Lemma move_cursor_row_in_bounds :
  forall up p,
    prow p < board_height ->
    prow (move_cursor_row up p) < board_height.
Proof.
  intros up p Hrow.
  unfold move_cursor_row.
  destruct up; simpl.
  - lia.
  - unfold board_height in *. simpl in *. lia.
Qed.

(** Horizontal cursor movement stays within the board bounds. *)
Lemma move_cursor_col_in_bounds :
  forall left p,
    pcol p < board_width ->
    pcol (move_cursor_col left p) < board_width.
Proof.
  intros left p Hcol.
  unfold move_cursor_col.
  destruct left; simpl.
  - lia.
  - unfold board_width in *. simpl in *. lia.
Qed.

(** Setting the cursor to an in-bounds position preserves the cursor-bounds invariant. *)
Lemma set_cursor_in_bounds :
  forall p gs,
    prow p < board_height ->
    pcol p < board_width ->
    cursor_in_bounds (set_cursor p gs).
Proof.
  intros p gs Hrow Hcol.
  unfold cursor_in_bounds, set_cursor.
  simpl.
  auto.
Qed.

(** The initial state starts with an in-bounds cursor. *)
Lemma initial_state_cursor_in_bounds :
  forall seed0,
    cursor_in_bounds (initial_state seed0).
Proof.
  intros seed0.
  unfold cursor_in_bounds, initial_state, board_height, board_width.
  simpl.
  lia.
Qed.

(** Restarting the game restores an in-bounds cursor. *)
Lemma restart_state_cursor_in_bounds :
  forall gs,
    cursor_in_bounds (restart_state gs).
Proof.
  intros gs.
  unfold restart_state.
  apply initial_state_cursor_in_bounds.
Qed.

(** A reveal click outside the board has no effect. *)
Lemma mouse_reveal_outside_noop :
  forall mx my gs,
    mouse_board_pos mx my = None ->
    mouse_reveal mx my gs = gs.
Proof.
  intros mx my gs Hmouse.
  unfold mouse_reveal.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A flag click outside the board has no effect. *)
Lemma mouse_flag_outside_noop :
  forall mx my gs,
    mouse_board_pos mx my = None ->
    mouse_flag mx my gs = gs.
Proof.
  intros mx my gs Hmouse.
  unfold mouse_flag.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A reveal click inside the board becomes reveal-at-cursor after moving the cursor. *)
Lemma mouse_reveal_inside :
  forall mx my p gs,
    mouse_board_pos mx my = Some p ->
    mouse_reveal mx my gs = reveal_at_cursor (set_cursor p gs).
Proof.
  intros mx my p gs Hmouse.
  unfold mouse_reveal.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A flag click inside the board becomes flag-at-cursor after moving the cursor. *)
Lemma mouse_flag_inside :
  forall mx my p gs,
    mouse_board_pos mx my = Some p ->
    mouse_flag mx my gs = toggle_flag_at_cursor (set_cursor p gs).
Proof.
  intros mx my p gs Hmouse.
  unfold mouse_flag.
  rewrite Hmouse.
  reflexivity.
Qed.

(** The quit event always sets the quit flag in the event handler result. *)
Lemma handle_event_quit_flag :
  forall mx my gs,
    fst (handle_event 1 mx my gs) = true.
Proof.
  reflexivity.
Qed.

(** The restart event always returns the restarted game state. *)
Lemma handle_event_restart_state :
  forall mx my gs,
    snd (handle_event 8 mx my gs) = restart_state gs.
Proof.
  reflexivity.
Qed.

(** Unknown events leave the game state unchanged and do not request quit. *)
Lemma handle_event_unknown_noop :
  forall ev mx my gs,
    10 < ev ->
    handle_event ev mx my gs = (false, gs).
Proof.
  intros ev mx my gs Hev.
  unfold handle_event.
  destruct ev as [|[|[|[|[|[|[|[|[|[|[|ev]]]]]]]]]]]; try lia; reflexivity.
Qed.

(** Every modeled interaction step preserves nonnegativity of the flag count. *)
Theorem pure_interaction_step_flagged_total_nonnegative :
  forall gs gs',
    pure_interaction_step gs gs' ->
    0 <= flagged_total (board gs').
Proof.
  intros gs gs' Hstep.
  inversion Hstep; subst; simpl; apply flagged_total_nonnegative.
Qed.
