From Stdlib Require Import Lia Bool PeanoNat.
From RocqsweeperGame Require Import SDL Rocqsweeper GameProofs.

Import Rocqsweeper.

(** * Cursor and input-mapping layer *)

Inductive pure_interaction_step : game_state -> game_state -> Prop :=
| PureInteractionSetCursor : forall p gs,
    pure_interaction_step gs (set_cursor p gs)
| PureInteractionSyncCursor : forall (mp : nat * nat) gs,
    pure_interaction_step gs (sync_cursor_with_mouse mp gs)
| PureInteractionMouseReveal : forall (mp : nat * nat) gs,
    pure_interaction_step gs (mouse_reveal mp gs)
| PureInteractionMouseFlag : forall (mp : nat * nat) gs,
    pure_interaction_step gs (mouse_flag mp gs).

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

(** Mouse synchronization is a no-op when the pointer is outside the board. *)
Lemma sync_cursor_with_mouse_outside :
  forall mp gs,
    mouse_board_pos mp = None ->
    sync_cursor_with_mouse mp gs = gs.
Proof.
  intros mp gs Hmouse.
  unfold sync_cursor_with_mouse, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** Mouse synchronization sets the cursor to the hovered board cell. *)
Lemma sync_cursor_with_mouse_inside :
  forall mp p gs,
    mouse_board_pos mp = Some p ->
    sync_cursor_with_mouse mp gs = set_cursor p gs.
Proof.
  intros mp p gs Hmouse.
  unfold sync_cursor_with_mouse, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** Mouse synchronization does not change the hidden-safe-cell count. *)
Lemma sync_cursor_with_mouse_hidden_safe_total :
  forall mp gs,
    hidden_safe_total (board (sync_cursor_with_mouse mp gs)) =
    hidden_safe_total (board gs).
Proof.
  intros mp gs.
  unfold sync_cursor_with_mouse, with_mouse_board_pos.
  destruct (mouse_board_pos mp); simpl; reflexivity.
Qed.

(** Mouse synchronization does not change the flag count. *)
Lemma sync_cursor_with_mouse_flagged_total :
  forall mp gs,
    flagged_total (board (sync_cursor_with_mouse mp gs)) =
    flagged_total (board gs).
Proof.
  intros mp gs.
  unfold sync_cursor_with_mouse, with_mouse_board_pos.
  destruct (mouse_board_pos mp); simpl; reflexivity.
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
  forall mp gs,
    mouse_board_pos mp = None ->
    mouse_reveal mp gs = gs.
Proof.
  intros mp gs Hmouse.
  unfold mouse_reveal, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A flag click outside the board has no effect. *)
Lemma mouse_flag_outside_noop :
  forall mp gs,
    mouse_board_pos mp = None ->
    mouse_flag mp gs = gs.
Proof.
  intros mp gs Hmouse.
  unfold mouse_flag, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A reveal click inside the board becomes reveal-at-cursor after moving the cursor. *)
Lemma mouse_reveal_inside :
  forall mp p gs,
    mouse_board_pos mp = Some p ->
    mouse_reveal mp gs = reveal_at_cursor (set_cursor p gs).
Proof.
  intros mp p gs Hmouse.
  unfold mouse_reveal, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** A flag click inside the board becomes flag-at-cursor after moving the cursor. *)
Lemma mouse_flag_inside :
  forall mp p gs,
    mouse_board_pos mp = Some p ->
    mouse_flag mp gs = toggle_flag_at_cursor (set_cursor p gs).
Proof.
  intros mp p gs Hmouse.
  unfold mouse_flag, with_mouse_board_pos.
  rewrite Hmouse.
  reflexivity.
Qed.

(** The quit event always sets the quit flag in the event handler result. *)
Lemma handle_event_quit_flag :
  forall gs,
    fst (handle_event EventQuit gs) = true.
Proof.
  reflexivity.
Qed.

(** The restart key always returns the restarted game state. *)
Lemma handle_event_restart_state :
  forall gs,
    snd (handle_event (EventKeyDown KeyR) gs) = restart_state gs.
Proof.
  reflexivity.
Qed.

(** Key release events are ignored by the event handler. *)
Lemma handle_event_key_up_noop :
  forall key gs,
    handle_event (EventKeyUp key) gs = (false, gs).
Proof.
  reflexivity.
Qed.

(** Empty polls leave the game state unchanged and do not request quit. *)
Lemma handle_event_none_noop :
  forall gs,
    handle_event EventNone gs = (false, gs).
Proof.
  reflexivity.
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
