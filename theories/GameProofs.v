From Stdlib Require Import Lia Bool PeanoNat Lists.List.
Import ListNotations.
From RocqsweeperGame Require Import Rocqsweeper.

Import Rocqsweeper.

(** One pure gameplay transition: reveal, flag, or restart. *)
Inductive pure_game_step : game_state -> game_state -> Prop :=
| PureGameReveal : forall gs,
    pure_game_step gs (reveal_at_cursor gs)
| PureGameFlag : forall gs,
    pure_game_step gs (toggle_flag_at_cursor gs)
| PureGameRestart : forall gs,
    pure_game_step gs (restart_state gs).

(** Predicate saying that a position lies inside the board. *)
Definition position_in_bounds (p : position) : Prop :=
  prow p < board_height /\ pcol p < board_width.

(** Predicate saying that a row has the expected board width. *)
Definition row_wf (row : list tile) : Prop :=
  length row = board_width.

(** Predicate saying that a board has the expected shape. *)
Definition well_formed_board (b : list (list tile)) : Prop :=
  length b = board_height /\ Forall row_wf b.

(** Predicate saying that both the board and cursor are in bounds. *)
Definition well_formed_state (gs : game_state) : Prop :=
  well_formed_board (board gs) /\ position_in_bounds (cursor gs).

(** Pointwise equality of mine bits across two boards. *)
Definition same_mine_layout (b1 b2 : list (list tile)) : Prop :=
  forall p,
    position_in_bounds p ->
    tile_mine (get_tile_pos p b1) = tile_mine (get_tile_pos p b2).

(** Pointwise equality of mine bits and adjacent counts across two boards. *)
Definition same_mine_adj_layout (b1 b2 : list (list tile)) : Prop :=
  forall p,
    position_in_bounds p ->
    tile_mine (get_tile_pos p b1) = tile_mine (get_tile_pos p b2) /\
    tile_adjacent (get_tile_pos p b1) = tile_adjacent (get_tile_pos p b2).

(** Replacing one list element does not change the length of the list. *)
Lemma length_replace_nth :
  forall (A : Type) n (xs : list A) x,
    length (replace_nth n xs x) = length xs.
Proof.
  intros A n xs x.
  revert n.
  induction xs as [|y ys IH]; intros [|n]; simpl; auto.
Qed.

(** Reading back the position that was just replaced returns the new value. *)
Lemma nth_replace_nth_eq :
  forall (A : Type) n (xs : list A) x d,
    n < length xs ->
    nth n (replace_nth n xs x) d = x.
Proof.
  intros A n xs x d.
  revert n.
  induction xs as [|y ys IH]; intros [|n] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

(** Replacing one position leaves every other list position unchanged. *)
Lemma nth_replace_nth_neq :
  forall (A : Type) i n (xs : list A) x d,
    i <> n ->
    nth i (replace_nth n xs x) d = nth i xs d.
Proof.
  intros A i n xs x d Hneq.
  revert i n Hneq.
  induction xs as [|y ys IH]; intros [|i] [|n] Hneq; simpl; auto; try contradiction.
Qed.

(** A pointwise predicate is preserved when a list element is replaced by another element satisfying it. *)
Lemma Forall_replace_nth :
  forall (A : Type) (P : A -> Prop) xs n x,
    Forall P xs ->
    P x ->
    Forall P (replace_nth n xs x).
Proof.
  intros A P xs.
  induction xs as [|y ys IH]; intros [|n] x Hall Hx; simpl.
  - constructor.
  - constructor.
  - inversion Hall; subst. constructor; auto.
  - inversion Hall; subst. constructor; auto.
Qed.

(** Any in-bounds element of a list satisfies a predicate that holds for the whole list. *)
Lemma Forall_nth :
  forall (A : Type) (P : A -> Prop) xs d n,
    Forall P xs ->
    n < length xs ->
    P (nth n xs d).
Proof.
  intros A P xs d n Hall.
  revert n Hall.
  induction xs as [|x xs IH]; intros [|n] Hall Hlt; simpl in *.
  - lia.
  - lia.
  - inversion Hall; subst; auto.
  - inversion Hall; subst. apply IH; auto. lia.
Qed.

(** Every in-bounds entry of a repeated blank-tile row is the blank tile. *)
Lemma nth_repeat_tile_blank :
  forall n i,
    i < n ->
    nth i (repeat_tile n) blank_tile = blank_tile.
Proof.
  intros n i.
  revert i.
  induction n as [|n IH]; intros [|i] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

(** Every in-bounds row of a repeated blank board is the standard blank row. *)
Lemma nth_repeat_board_row :
  forall h i,
    i < h ->
    nth i (repeat_board h) [] = repeat_tile board_width.
Proof.
  intros h i.
  revert i.
  induction h as [|h IH]; intros [|i] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

(** A repeated blank-tile row has the requested length. *)
Lemma repeat_tile_length :
  forall n,
    length (repeat_tile n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** A repeated blank board has the requested number of rows. *)
Lemma repeat_board_length :
  forall h,
    length (repeat_board h) = h.
Proof.
  induction h; simpl; auto.
Qed.

(** Every row in a repeated blank board has the expected width. *)
Lemma repeat_board_Forall :
  forall h,
    Forall row_wf (repeat_board h).
Proof.
  induction h; simpl; constructor; auto.
  unfold row_wf. simpl. reflexivity.
Qed.

(** The blank board has the expected rectangular shape. *)
Lemma blank_board_wf :
  well_formed_board blank_board.
Proof.
  unfold well_formed_board, blank_board.
  split.
  - apply repeat_board_length.
  - apply repeat_board_Forall.
Qed.

(** Any in-bounds row of a well-formed board has the expected width. *)
Lemma nth_row_wf :
  forall b row,
    well_formed_board b ->
    row < board_height ->
    length (nth row b []) = board_width.
Proof.
  intros b row [Hlen Hall] Hrow.
  apply (Forall_nth _ _ b [] row) in Hall.
  - exact Hall.
  - rewrite Hlen. exact Hrow.
Qed.

(** Updating a well-formed in-bounds cell makes that cell read back as the new tile. *)
Lemma get_tile_set_tile_same :
  forall b row col t,
    well_formed_board b ->
    row < board_height ->
    col < board_width ->
    get_tile row col (set_tile row col t b) = t.
Proof.
  intros b row col t Hwf Hrow Hcol.
  unfold get_tile, set_tile.
  destruct Hwf as [Hlen Hall].
  rewrite nth_replace_nth_eq.
  2: rewrite Hlen; exact Hrow.
  rewrite nth_replace_nth_eq.
  2: rewrite (nth_row_wf b row (conj Hlen Hall) Hrow); exact Hcol.
  reflexivity.
Qed.

(** Updating one in-bounds cell of a well-formed board does not affect any different cell. *)
Lemma get_tile_set_tile_other :
  forall b row col row' col' t,
    well_formed_board b ->
    row < board_height ->
    col < board_width ->
    row <> row' \/ col <> col' ->
    get_tile row col (set_tile row' col' t b) = get_tile row col b.
Proof.
  intros b row col row' col' t Hwf Hrow Hcol Hneq.
  unfold get_tile, set_tile.
  destruct Hwf as [Hlen Hall].
  destruct (Nat.eq_dec row row') as [Heqrow|Hneqrow].
  - subst row'.
    rewrite nth_replace_nth_eq.
    2: rewrite Hlen; exact Hrow.
    assert (Hcolneq : col <> col').
    { destruct Hneq as [Hbad|Hbad].
      - contradiction.
      - exact Hbad. }
    rewrite nth_replace_nth_neq; auto.
  - rewrite nth_replace_nth_neq; auto.
Qed.

(** Updating an in-bounds cell preserves board well-formedness. *)
Lemma set_tile_wf :
  forall b row col t,
    well_formed_board b ->
    row < board_height ->
    col < board_width ->
    well_formed_board (set_tile row col t b).
Proof.
  intros b row col t [Hlen Hall] Hrow Hcol.
  unfold well_formed_board, set_tile.
  split.
  - rewrite length_replace_nth. exact Hlen.
  - apply Forall_replace_nth; auto.
    unfold row_wf. rewrite length_replace_nth.
    apply nth_row_wf with (row := row). split; assumption. exact Hrow.
Qed.

(** Position-based cell updates preserve board well-formedness. *)
Lemma set_tile_pos_wf :
  forall b p t,
    well_formed_board b ->
    position_in_bounds p ->
    well_formed_board (set_tile_pos p t b).
Proof.
  intros b [row col] t Hwf [Hrow Hcol].
  unfold set_tile_pos.
  apply set_tile_wf; auto.
Qed.

(** Every initial state starts with a well-formed board and an in-bounds cursor. *)
Lemma initial_state_wf :
  forall seed0,
    well_formed_state (initial_state seed0).
Proof.
  intros seed0.
  unfold well_formed_state, initial_state, position_in_bounds.
  split.
  - apply blank_board_wf.
  - simpl. unfold board_height, board_width. lia.
Qed.

(** Restarting the game returns to a well-formed state. *)
Lemma restart_state_wf :
  forall gs,
    well_formed_state (restart_state gs).
Proof.
  intros gs. unfold restart_state. apply initial_state_wf.
Qed.

(** The total number of flagged cells is never negative. *)
Theorem flagged_total_nonnegative :
  forall b, 0 <= flagged_total b.
Proof.
  induction b as [|row rest IH]; simpl; [lia|].
  induction row as [|t row IHrow]; simpl; lia.
Qed.

(** The total number of hidden safe cells is never negative. *)
Theorem hidden_safe_total_nonnegative :
  forall b, 0 <= hidden_safe_total b.
Proof.
  induction b as [|row rest IH]; simpl; [lia|].
  induction row as [|t row IHrow]; simpl; lia.
Qed.

(** On the blank board, every cell counts as a hidden safe cell. *)
Lemma hidden_safe_total_blank_board :
  hidden_safe_total blank_board = total_cells.
Proof.
  reflexivity.
Qed.

(** Restarting always returns the game to the Playing phase. *)
Lemma restart_state_phase :
  forall gs, game_phase (restart_state gs) = Playing.
Proof.
  intros gs. unfold restart_state, initial_state. reflexivity.
Qed.

(** Restarting always restores the first-reveal state. *)
Lemma restart_state_waiting :
  forall gs, waiting_for_first_reveal (restart_state gs) = true.
Proof.
  intros gs. unfold restart_state, initial_state. reflexivity.
Qed.

(** Restarting restores the full hidden-safe-cell count. *)
Lemma restart_state_hidden_safe_total :
  forall gs,
    hidden_safe_total (board (restart_state gs)) = total_cells.
Proof.
  intros gs. unfold restart_state, initial_state, blank_board. reflexivity.
Qed.

(** Restarting clears the flag count. *)
Lemma restart_state_flagged_total :
  forall gs,
    flagged_total (board (restart_state gs)) = 0.
Proof.
  intros gs. unfold restart_state, initial_state, blank_board. reflexivity.
Qed.

(** Restarting replaces the current board with the blank board. *)
Theorem restart_state_clean_blank_board :
  forall gs,
    board (restart_state gs) = blank_board.
Proof.
  reflexivity.
Qed.

(** Every in-bounds tile after restart is the blank tile. *)
Theorem restart_state_clean_blank_tile :
  forall gs p,
    position_in_bounds p ->
    get_tile_pos p (board (restart_state gs)) = blank_tile.
Proof.
  intros gs [row col] [Hrow Hcol].
  unfold restart_state, initial_state, board, blank_board, get_tile_pos, get_tile.
  rewrite nth_repeat_board_row by exact Hrow.
  apply nth_repeat_tile_blank. exact Hcol.
Qed.

(** Reveal is a no-op once the game is already won or lost. *)
Lemma reveal_at_cursor_terminal_noop :
  forall gs,
    game_phase gs = Won \/ game_phase gs = Lost ->
    reveal_at_cursor gs = gs.
Proof.
  intros gs Hphase.
  unfold reveal_at_cursor, reveal_playing_from_board, reveal_playing_result_phase, reveal_playing_result_board, reveal_playing_source_tile.
  destruct (game_phase gs); try reflexivity.
  destruct Hphase as [Hwon | Hlost]; discriminate.
Qed.

(** Flag toggling is a no-op once the game is already won or lost. *)
Lemma toggle_flag_at_cursor_terminal_noop :
  forall gs,
    game_phase gs = Won \/ game_phase gs = Lost ->
    toggle_flag_at_cursor gs = gs.
Proof.
  intros gs Hphase.
  unfold toggle_flag_at_cursor.
  destruct (game_phase gs); try reflexivity.
  destruct Hphase as [Hwon | Hlost]; discriminate.
Qed.

(** Rebuilding a state with a board clears the first-reveal flag. *)
Lemma state_with_board_waiting_false :
  forall gs b, waiting_for_first_reveal (state_with_board gs b) = false.
Proof.
  reflexivity.
Qed.

(** Rebuilding a state with a board stores exactly that board. *)
Lemma state_with_board_board :
  forall gs b, board (state_with_board gs b) = b.
Proof.
  reflexivity.
Qed.

(** Rebuilding a state with a board updates the phase to Won exactly when no safe cells remain hidden. *)
Lemma state_with_board_phase :
  forall gs b,
    game_phase (state_with_board gs b) =
    if Nat.eqb (hidden_safe_total b) 0 then Won else game_phase gs.
Proof.
  reflexivity.
Qed.

(** Toggling a flag does not change whether a tile contains a mine. *)
Lemma tile_toggle_flag_preserves_mine :
  forall t,
    tile_mine (tile_toggle_flag t) = tile_mine t.
Proof.
  intros [m r f a]. reflexivity.
Qed.

(** Toggling a flag does not change a tile's adjacent-mine count. *)
Lemma tile_toggle_flag_preserves_adjacent :
  forall t,
    tile_adjacent (tile_toggle_flag t) = tile_adjacent t.
Proof.
  intros [m r f a]. reflexivity.
Qed.

(** Reading back the position just updated returns the inserted tile. *)
Lemma get_tile_pos_set_tile_pos_same :
  forall b p t,
    well_formed_board b ->
    position_in_bounds p ->
    get_tile_pos p (set_tile_pos p t b) = t.
Proof.
  intros b [row col] t Hwf [Hrow Hcol].
  unfold get_tile_pos, set_tile_pos.
  apply get_tile_set_tile_same; auto.
Qed.

(** Updating one board position does not change the tile at any different position. *)
Lemma get_tile_pos_set_tile_pos_other :
  forall b p q t,
    well_formed_board b ->
    position_in_bounds p ->
    p <> q ->
    get_tile_pos p (set_tile_pos q t b) = get_tile_pos p b.
Proof.
  intros b [row col] [row' col'] t Hwf [Hrow Hcol] Hneq.
  unfold get_tile_pos, set_tile_pos.
  apply get_tile_set_tile_other; auto.
  destruct (Nat.eq_dec row row') as [Heqrow|Hneqrow].
  - subst row'. right. intro Heqcol. apply Hneq. f_equal; exact Heqcol.
  - left. exact Hneqrow.
Qed.

(** Replacing a tile with one that has the same mine bit preserves the whole board's mine layout. *)
Lemma set_tile_pos_preserves_mine_layout :
  forall b p t,
    well_formed_board b ->
    position_in_bounds p ->
    tile_mine t = tile_mine (get_tile_pos p b) ->
    same_mine_layout (set_tile_pos p t b) b.
Proof.
  intros b p t Hwf Hp Hmine q Hq.
  destruct (Nat.eq_dec (prow q) (prow p)) as [Hrow|Hrow];
    destruct (Nat.eq_dec (pcol q) (pcol p)) as [Hcol|Hcol].
  - assert (Heq : q = p).
    { destruct q as [qr qc], p as [pr pc]; simpl in *; subst; f_equal; assumption. }
    subst q.
    rewrite get_tile_pos_set_tile_pos_same by assumption.
    exact Hmine.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    reflexivity.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    reflexivity.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    reflexivity.
Qed.

(** Replacing a tile with one that has the same mine bit and adjacency count preserves that combined layout everywhere. *)
Lemma set_tile_pos_preserves_mine_adj_layout :
  forall b p t,
    well_formed_board b ->
    position_in_bounds p ->
    tile_mine t = tile_mine (get_tile_pos p b) ->
    tile_adjacent t = tile_adjacent (get_tile_pos p b) ->
    same_mine_adj_layout (set_tile_pos p t b) b.
Proof.
  intros b p t Hwf Hp Hmine Hadj q Hq.
  destruct (Nat.eq_dec (prow q) (prow p)) as [Hrow|Hrow];
    destruct (Nat.eq_dec (pcol q) (pcol p)) as [Hcol|Hcol].
  - assert (Heq : q = p).
    { destruct q as [qr qc], p as [pr pc]; simpl in *; subst; f_equal; assumption. }
    subst q.
    rewrite get_tile_pos_set_tile_pos_same by assumption.
    split; assumption.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    split; reflexivity.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    split; reflexivity.
  - rewrite get_tile_pos_set_tile_pos_other by (assumption || (intro H; inversion H; congruence)).
    split; reflexivity.
Qed.

(** Equality of mine bits and adjacency counts implies equality of mine bits alone. *)
Lemma same_mine_adj_layout_implies_mine_layout :
  forall b1 b2,
    same_mine_adj_layout b1 b2 ->
    same_mine_layout b1 b2.
Proof.
  intros b1 b2 Hsame p Hp.
  specialize (Hsame p Hp).
  tauto.
Qed.

(** Flag toggling leaves the board's mine placement unchanged. *)
Theorem toggle_flag_at_cursor_preserves_mine_layout :
  forall gs,
    well_formed_state gs ->
    same_mine_layout (board (toggle_flag_at_cursor gs)) (board gs).
Proof.
  intros gs [Hwf Hcur] p Hp.
  unfold toggle_flag_at_cursor.
  destruct (game_phase gs); simpl; try reflexivity.
  remember (get_tile_pos (cursor gs) (board gs)) as t.
  destruct (tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)); [reflexivity|].
  apply set_tile_pos_preserves_mine_layout; auto.
  rewrite Heqt. apply tile_toggle_flag_preserves_mine.
Qed.

(** Flag toggling changes only flag state, not mines or adjacency counts. *)
Theorem toggle_flag_at_cursor_changes_only_flags :
  forall gs,
    well_formed_state gs ->
    same_mine_adj_layout (board (toggle_flag_at_cursor gs)) (board gs).
Proof.
  intros gs [Hwf Hcur] p Hp.
  unfold toggle_flag_at_cursor.
  destruct (game_phase gs); simpl; try (split; reflexivity).
  remember (get_tile_pos (cursor gs) (board gs)) as t.
  destruct (tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)); [split; reflexivity|].
  apply set_tile_pos_preserves_mine_adj_layout; auto.
  - rewrite Heqt. apply tile_toggle_flag_preserves_mine.
  - rewrite Heqt. apply tile_toggle_flag_preserves_adjacent.
Qed.





(** Every in-bounds board position flattens to an index below the total number of cells. *)
Lemma board_index_lt_total_cells :
  forall p,
    position_in_bounds p ->
    board_index p < total_cells.
Proof.
  intros [row col] [Hrow Hcol].
  unfold board_index, total_cells, board_height, board_width in *.
  simpl in *.
  lia.
Qed.

(** Every linear board index below the board size maps back to an in-bounds position. *)
Lemma index_pos_in_bounds :
  forall idx,
    idx < total_cells ->
    position_in_bounds (index_pos idx).
Proof.
  intros idx Hidx.
  unfold index_pos, index_row, index_col, position_in_bounds,
    total_cells, board_width, board_height in *.
  simpl in *.
  split.
  - change (idx / 9 < 9).
    apply Nat.Div0.div_lt_upper_bound.
    lia.
  - change (idx mod 9 < 9).
    apply Nat.mod_upper_bound.
    lia.
Qed.

(** Flattening a valid linear index after converting it to a position returns the same index. *)
Lemma board_index_index_pos :
  forall idx,
    idx < total_cells ->
    board_index (index_pos idx) = idx.
Proof.
  intros idx Hidx.
  unfold board_index, index_pos, index_row, index_col, board_width.
  simpl.
  change ((idx / 9) * 9 + idx mod 9 = idx).
  rewrite Nat.mul_comm.
  symmetry.
  apply Nat.div_mod.
  lia.
Qed.


(** Two in-bounds positions with the same flattened index must be the same position. *)
Lemma board_index_injective :
  forall p q,
    position_in_bounds p ->
    position_in_bounds q ->
    board_index p = board_index q ->
    p = q.
Proof.
  intros [r1 c1] [r2 c2] [Hr1 Hc1] [Hr2 Hc2] Heq.
  unfold board_index, board_width in Heq.
  simpl in Heq.
  unfold board_height, board_width in Hr1, Hc1, Hr2, Hc2.
  simpl in Hr1, Hc1, Hr2, Hc2.
  assert (Hmod : (r1 * 9 + c1) mod 9 = (r2 * 9 + c2) mod 9) by now rewrite Heq.
  replace ((r1 * 9 + c1) mod 9) with c1 in Hmod.
  2:{ rewrite Nat.add_comm. rewrite Nat.Div0.mod_add. symmetry. apply Nat.mod_small. lia. }
  replace ((r2 * 9 + c2) mod 9) with c2 in Hmod.
  2:{ rewrite Nat.add_comm. rewrite Nat.Div0.mod_add. symmetry. apply Nat.mod_small. lia. }
  assert (Hc : c1 = c2) by exact Hmod.
  assert (Hr : r1 = r2) by lia.
  subst. reflexivity.
Qed.

(** Converting an in-bounds position to an index and back returns the original position. *)
Lemma index_pos_board_index :
  forall p,
    position_in_bounds p ->
    index_pos (board_index p) = p.
Proof.
  intros p Hp.
  apply board_index_injective.
  - apply index_pos_in_bounds.
    apply board_index_lt_total_cells.
    exact Hp.
  - exact Hp.
  - apply board_index_index_pos.
    apply board_index_lt_total_cells.
    exact Hp.
Qed.

(** Annotating a row changes adjacency counts but leaves mine bits unchanged. *)
Lemma annotate_row_nth_mine :
  forall row col0 cells b col,
    tile_mine (nth col (annotate_row row col0 cells b) blank_tile) =
    tile_mine (nth col cells blank_tile).
Proof.
  intros row col0 cells b col.
  revert col0 col.
  induction cells as [|t rest IH]; intros col0 [|col]; simpl; auto.
Qed.

(** Annotating all rows leaves the mine bit unchanged at every cell. *)
Lemma annotate_board_rows_get_tile_mine :
  forall start rows b row col,
    tile_mine (get_tile row col (annotate_board_rows start rows b)) =
    tile_mine (get_tile row col rows).
Proof.
  intros start rows b row col.
  revert start row.
  induction rows as [|cells rest IH]; intros start [|row]; simpl; auto.
  - apply annotate_row_nth_mine.
  - apply IH.
Qed.

(** Board annotation preserves the entire mine layout. *)
Lemma annotate_board_preserves_mine_layout :
  forall b,
    same_mine_layout (annotate_board b) b.
Proof.
  intros b p Hp.
  destruct p as [row col].
  unfold annotate_board, same_mine_layout, get_tile_pos.
  apply annotate_board_rows_get_tile_mine.
Qed.

(** Annotating a row preserves its length. *)
Lemma annotate_row_length :
  forall row col cells b,
    length (annotate_row row col cells b) = length cells.
Proof.
  intros row col cells b.
  revert col.
  induction cells as [|t rest IH]; intros col; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Annotating each row preserves the number of rows in the board. *)
Lemma annotate_board_rows_length :
  forall row rows b,
    length (annotate_board_rows row rows b) = length rows.
Proof.
  intros row rows b.
  revert row.
  induction rows as [|cells rest IH]; intros row; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Annotating a well-formed row preserves its width. *)
Lemma annotate_row_wf :
  forall row col cells b,
    row_wf cells ->
    row_wf (annotate_row row col cells b).
Proof.
  intros row col cells b Hwf.
  unfold row_wf in *.
  rewrite annotate_row_length.
  exact Hwf.
Qed.

(** Annotating all rows of a well-formed board preserves row widths. *)
Lemma annotate_board_rows_Forall :
  forall row rows b,
    Forall row_wf rows ->
    Forall row_wf (annotate_board_rows row rows b).
Proof.
  intros row rows b Hall.
  revert row.
  induction Hall; intros row; simpl.
  - constructor.
  - constructor.
    + apply annotate_row_wf. exact H.
    + apply IHHall.
Qed.

(** Annotating a well-formed board preserves its rectangular shape. *)
Lemma annotate_board_wf :
  forall b,
    well_formed_board b ->
    well_formed_board (annotate_board b).
Proof.
  intros b [Hlen Hall].
  unfold annotate_board, well_formed_board.
  split.
  - rewrite annotate_board_rows_length. exact Hlen.
  - apply annotate_board_rows_Forall. exact Hall.
Qed.

(** Mine placement preserves the rectangular shape of the board. *)
Lemma place_mines_wf :
  forall fuel mines_left cur_seed safe_idx b,
    well_formed_board b ->
    well_formed_board (place_mines fuel mines_left cur_seed safe_idx b).
Proof.
  induction fuel as [|fuel IH]; intros mines_left cur_seed safe_idx b Hwf; simpl; auto.
  destruct mines_left as [|mines_left']; auto.
  set (idx := Nat.modulo cur_seed total_cells).
  set (p := index_pos idx).
  set (t := get_tile_pos p b).
  change (well_formed_board
    (if Nat.eqb idx safe_idx || tile_mine t
     then place_mines fuel (S mines_left') (next_seed cur_seed) safe_idx b
     else place_mines fuel mines_left' (next_seed cur_seed) safe_idx
            (set_tile_pos p (tile_with_mine t) b))).
  destruct (Nat.eqb idx safe_idx || tile_mine t) eqn:Hskip.
  - apply IH. exact Hwf.
  - apply IH.
    apply set_tile_pos_wf; auto.
    subst p idx.
    apply index_pos_in_bounds.
    apply Nat.mod_upper_bound.
    unfold total_cells, board_height, board_width.
    simpl. lia.
Qed.


(** Distinct bounded linear indices map to distinct board positions. *)
Lemma index_pos_injective_bounded :
  forall i j,
    i < total_cells ->
    j < total_cells ->
    index_pos i = index_pos j ->
    i = j.
Proof.
  intros i j Hi Hj Heq.
  assert (Hbi : board_index (index_pos i) = i).
  { apply board_index_index_pos. exact Hi. }
  assert (Hbj : board_index (index_pos j) = j).
  { apply board_index_index_pos. exact Hj. }
  rewrite Heq in Hbi.
  rewrite Hbj in Hbi.
  symmetry. exact Hbi.
Qed.

(** Any valid position on the blank board is guaranteed to be non-mine. *)
Lemma blank_board_safe_nonmine :
  forall safe_idx,
    safe_idx < total_cells ->
    tile_mine (get_tile_pos (index_pos safe_idx) blank_board) = false.
Proof.
  intros safe_idx Hsafe.
  assert (Hp : position_in_bounds (index_pos safe_idx)).
  { apply index_pos_in_bounds. exact Hsafe. }
  destruct (index_pos safe_idx) as [row col].
  destruct Hp as [Hrow Hcol].
  unfold blank_board, get_tile_pos, get_tile.
  rewrite nth_repeat_board_row by exact Hrow.
  rewrite nth_repeat_tile_blank by exact Hcol.
  reflexivity.
Qed.


(** Every in-bounds position on the blank board is non-mine. *)
Lemma blank_board_nonmine_at :
  forall p,
    position_in_bounds p ->
    tile_mine (get_tile_pos p blank_board) = false.
Proof.
  intros p Hp.
  assert (Hmine' : tile_mine (get_tile_pos (index_pos (board_index p)) blank_board) = false).
  { apply blank_board_safe_nonmine.
    apply board_index_lt_total_cells. exact Hp. }
  assert (Hpos :
    get_tile_pos p blank_board =
    get_tile_pos (index_pos (board_index p)) blank_board).
  { rewrite <- (index_pos_board_index p Hp) at 1. reflexivity. }
  rewrite Hpos. exact Hmine'.
Qed.

(** Mine placement never puts a mine on the designated safe index. *)
Lemma place_mines_preserves_safe_position :
  forall fuel mines_left cur_seed safe_idx b,
    well_formed_board b ->
    safe_idx < total_cells ->
    tile_mine (get_tile_pos (index_pos safe_idx) b) = false ->
    tile_mine (get_tile_pos (index_pos safe_idx)
      (place_mines fuel mines_left cur_seed safe_idx b)) = false.
Proof.
  induction fuel as [|fuel IH]; intros mines_left cur_seed safe_idx b Hwf Hsafe Hmine; simpl; auto.
  destruct mines_left as [|mines_left']; auto.
  set (idx := Nat.modulo cur_seed total_cells).
  set (p := index_pos idx).
  set (t := get_tile_pos p b).
  set (next_board :=
    if Nat.eqb idx safe_idx || tile_mine t
    then place_mines fuel (S mines_left') (next_seed cur_seed) safe_idx b
    else place_mines fuel mines_left' (next_seed cur_seed) safe_idx
           (set_tile_pos p (tile_with_mine t) b)).
  change (tile_mine (get_tile_pos (index_pos safe_idx) next_board) = false).
  unfold next_board.
  destruct (Nat.eqb idx safe_idx || tile_mine t) eqn:Hskip.
  - apply IH; assumption.
  - apply IH.
    + apply set_tile_pos_wf; auto.
      subst p idx.
      apply index_pos_in_bounds.
      apply Nat.mod_upper_bound.
      unfold total_cells, board_height, board_width.
      simpl. lia.
    + exact Hsafe.
    + rewrite get_tile_pos_set_tile_pos_other.
      * exact Hmine.
      * exact Hwf.
      * apply index_pos_in_bounds. exact Hsafe.
      * intro Heq.
        apply orb_false_iff in Hskip.
        destruct Hskip as [Hneq _].
        apply Nat.eqb_neq in Hneq.
        assert (Hidx : idx < total_cells).
        { subst idx. apply Nat.mod_upper_bound. unfold total_cells, board_height, board_width. simpl. lia. }
        apply Hneq.
        apply index_pos_injective_bounded; auto.
Qed.

(** Generated boards keep the designated safe index non-mine before re-expressing it as a position. *)
Lemma generate_board_index_safe_nonmine :
  forall seed0 safe,
    position_in_bounds safe ->
    tile_mine
      (get_tile_pos (index_pos (board_index safe))
        (place_mines (total_cells * 6) mine_count seed0 (board_index safe) blank_board)) = false.
Proof.
  intros seed0 safe Hsafe.
  apply place_mines_preserves_safe_position.
  - apply blank_board_wf.
  - apply board_index_lt_total_cells. exact Hsafe.
  - apply blank_board_safe_nonmine.
    apply board_index_lt_total_cells. exact Hsafe.
Qed.


(** Mine placement preserves non-mine status at the designated safe position. *)
Lemma place_mines_preserves_nonmine_at :
  forall fuel mines_left cur_seed p b,
    well_formed_board b ->
    position_in_bounds p ->
    tile_mine (get_tile_pos p b) = false ->
    tile_mine (get_tile_pos p (place_mines fuel mines_left cur_seed (board_index p) b)) = false.
Proof.
  intros fuel mines_left cur_seed p b Hwf Hp Hmine.
  assert (Hmine' : tile_mine (get_tile_pos (index_pos (board_index p)) b) = false).
  { rewrite index_pos_board_index. exact Hmine. exact Hp. }
  assert (Hpos :
    get_tile_pos p (place_mines fuel mines_left cur_seed (board_index p) b) =
    get_tile_pos (index_pos (board_index p))
      (place_mines fuel mines_left cur_seed (board_index p) b)).
  { rewrite <- (index_pos_board_index p Hp) at 1. reflexivity. }
  rewrite Hpos.
  exact (place_mines_preserves_safe_position
    fuel mines_left cur_seed (board_index p) b Hwf
    (board_index_lt_total_cells p Hp) Hmine').
Qed.

(** Board generation never places a mine at the designated safe position. *)
Lemma generate_board_safe_nonmine :
  forall seed0 safe,
    position_in_bounds safe ->
    tile_mine (get_tile_pos safe (generate_board seed0 safe)) = false.
Proof.
  intros seed0 safe Hsafe.
  unfold generate_board.
  set (b := place_mines (total_cells * 6) mine_count seed0 (board_index safe) blank_board).
  assert (Hannot : tile_mine (get_tile_pos safe (annotate_board b)) = tile_mine (get_tile_pos safe b)).
  { apply annotate_board_preserves_mine_layout. exact Hsafe. }
  rewrite Hannot.
  subst b.
  apply place_mines_preserves_nonmine_at.
  - apply blank_board_wf.
  - exact Hsafe.
  - apply blank_board_nonmine_at.
    exact Hsafe.
Qed.

(** The first reveal position is guaranteed to be safe on the generated board. *)
Theorem first_reveal_is_safe :
  forall gs,
    well_formed_state gs ->
    waiting_for_first_reveal gs = true ->
    tile_mine (get_tile_pos (cursor gs) (generate_board (seed gs) (cursor gs))) = false.
Proof.
  intros gs [_ Hcur] Hwaiting.
  apply generate_board_safe_nonmine.
  exact Hcur.
Qed.




(** Every board has the same mine layout as itself. *)
Lemma same_mine_layout_refl :
  forall b,
    same_mine_layout b b.
Proof.
  intros b p Hp. reflexivity.
Qed.

(** Mine-layout equality composes transitively across intermediate boards. *)
Lemma same_mine_layout_trans :
  forall b1 b2 b3,
    same_mine_layout b1 b2 ->
    same_mine_layout b2 b3 ->
    same_mine_layout b1 b3.
Proof.
  intros b1 b2 b3 H12 H23 p Hp.
  rewrite H12 by exact Hp.
  apply H23. exact Hp.
Qed.

(** Revealing a tile and clearing its flag does not change its mine bit. *)
Lemma tile_reveal_clear_flag_preserves_mine :
  forall t,
    tile_mine (tile_reveal_clear_flag t) = tile_mine t.
Proof.
  intros [m r f a]. reflexivity.
Qed.

(** Adding an optional in-bounds position to a worklist preserves the in-bounds invariant. *)
Lemma append_if_Forall :
  forall p rest cond,
    Forall position_in_bounds rest ->
    (cond = true -> position_in_bounds p) ->
    Forall position_in_bounds (append_if cond p rest).
Proof.
  intros p rest cond Hrest Hp.
  unfold append_if.
  destruct cond; simpl.
  - constructor; auto.
  - exact Hrest.
Qed.

(** Taking the predecessor of a positive bounded number stays within the same bound. *)
Lemma pred_lt_of_nonzero :
  forall n bound,
    n < bound ->
    n <> 0 ->
    Nat.pred n < bound.
Proof.
  intros n bound Hlt Hnz.
  destruct n; simpl in *; lia.
Qed.

(** All neighbors generated for an in-bounds cell are themselves in bounds. *)
Lemma neighbors_in_bounds :
  forall p,
    position_in_bounds p ->
    Forall position_in_bounds (neighbors p).
Proof.
  intros [r c] [Hr Hc].
  unfold neighbors, has_up, has_left, has_down, has_right in *.
  unfold board_height, board_width in *.
  simpl in *.
  apply append_if_Forall.
  2:{ intro H.
      apply Bool.andb_true_iff in H as [Hd Hrgt].
      apply Nat.ltb_lt in Hd.
      apply Nat.ltb_lt in Hrgt.
      split; simpl; assumption. }
  apply append_if_Forall.
  2:{ intro Hd.
      apply Nat.ltb_lt in Hd.
      split; simpl; [exact Hd|exact Hc]. }
  apply append_if_Forall.
  2:{ intro H.
      apply Bool.andb_true_iff in H as [Hd Hl].
      apply Nat.ltb_lt in Hd.
      apply negb_true_iff in Hl.
      apply Nat.eqb_neq in Hl.
      split; simpl.
      - exact Hd.
      - apply pred_lt_of_nonzero; assumption. }
  apply append_if_Forall.
  2:{ intro Hrgt.
      apply Nat.ltb_lt in Hrgt.
      split; simpl; [exact Hr|exact Hrgt]. }
  apply append_if_Forall.
  2:{ intro Hl.
      apply negb_true_iff in Hl.
      apply Nat.eqb_neq in Hl.
      split; simpl.
      - exact Hr.
      - apply pred_lt_of_nonzero; assumption. }
  apply append_if_Forall.
  2:{ intro H.
      apply Bool.andb_true_iff in H as [Hu Hrgt].
      apply negb_true_iff in Hu.
      apply Nat.eqb_neq in Hu.
      apply Nat.ltb_lt in Hrgt.
      split; simpl.
      - apply pred_lt_of_nonzero; assumption.
      - exact Hrgt. }
  apply append_if_Forall.
  2:{ intro Hu.
      apply negb_true_iff in Hu.
      apply Nat.eqb_neq in Hu.
      split; simpl.
      - apply pred_lt_of_nonzero; assumption.
      - exact Hc. }
  apply append_if_Forall.
  2:{ intro H.
      apply Bool.andb_true_iff in H as [Hu Hl].
      apply negb_true_iff in Hu.
      apply Nat.eqb_neq in Hu.
      apply negb_true_iff in Hl.
      apply Nat.eqb_neq in Hl.
      split; simpl.
      - apply pred_lt_of_nonzero; assumption.
      - apply pred_lt_of_nonzero; assumption. }
  constructor.
Qed.


(** The recursive reveal flood-fill only changes visibility and flags, never mine placement. *)
Lemma reveal_region_preserves_mine_layout :
  forall fuel todo b,
    well_formed_board b ->
    Forall position_in_bounds todo ->
    same_mine_layout (reveal_region fuel todo b) b.
Proof.
  induction fuel as [|fuel IH]; intros todo b Hwf Htodo; simpl.
  - apply same_mine_layout_refl.
  - destruct todo as [|p rest].
    + apply same_mine_layout_refl.
    + inversion Htodo as [|p' rest' Hp Hrest]; subst.
      remember (get_tile_pos p b) as t.
      destruct (tile_revealed t || tile_flagged t || tile_mine t) eqn:Hstop.
      * apply IH; assumption.
      * set (b1 := set_tile_pos p (tile_reveal_clear_flag t) b).
        assert (Hwf1 : well_formed_board b1).
        { unfold b1. apply set_tile_pos_wf; assumption. }
        assert (Hsame1 : same_mine_layout b1 b).
        { unfold b1.
          apply set_tile_pos_preserves_mine_layout; auto.
          rewrite Heqt. apply tile_reveal_clear_flag_preserves_mine. }
        assert (Htodo' : Forall position_in_bounds
          (if Nat.eqb (tile_adjacent t) 0 then neighbors p ++ rest else rest)).
        {
          destruct (Nat.eqb (tile_adjacent t) 0); auto.
          apply Forall_app.
          split.
          - apply neighbors_in_bounds. exact Hp.
          - exact Hrest.
        }
        eapply same_mine_layout_trans.
        2: exact Hsame1.
        apply IH; assumption.
Qed.








(** Reflexive-transitive closure of the pure gameplay step relation.
    This is a convenient notion of whole-game execution trace for theorem sketches. *)
Inductive pure_game_trace : game_state -> game_state -> Prop :=
| PureGameTraceRefl : forall gs,
    pure_game_trace gs gs
| PureGameTraceStep : forall gs1 gs2 gs3,
    pure_game_step gs1 gs2 ->
    pure_game_trace gs2 gs3 ->
    pure_game_trace gs1 gs3.

(** Count a tile's contribution to the hidden-safe-cell measure. *)
Definition hidden_safe_weight (t : tile) : nat :=
  if tile_mine t || tile_revealed t then 0 else 1.

(** Replacing one row entry by a tile with no larger hidden-safe contribution
    cannot increase the hidden-safe count of that row. *)
Lemma hidden_safe_in_row_replace_nth_le :
  forall row i t,
    hidden_safe_weight t <= hidden_safe_weight (nth i row blank_tile) ->
    hidden_safe_in_row (replace_nth i row t) <= hidden_safe_in_row row.
Proof.
  induction row as [|x xs IH]; intros [|i] t Hle; simpl in *.
  - lia.
  - lia.
  - unfold hidden_safe_weight in Hle.
    simpl.
    lia.
  - apply Nat.add_le_mono_l.
    apply IH.
    exact Hle.
Qed.

(** Replacing one cell by a tile with no larger hidden-safe contribution
    cannot increase the hidden-safe count of the whole board. *)
Lemma hidden_safe_total_set_tile_le :
  forall b row col t,
    hidden_safe_weight t <= hidden_safe_weight (get_tile row col b) ->
    hidden_safe_total (set_tile row col t b) <= hidden_safe_total b.
Proof.
  induction b as [|r rows IH]; intros row col t Hle; simpl in *.
  - destruct row; simpl; lia.
  - destruct row as [|row'].
    + apply Nat.add_le_mono_r.
      apply hidden_safe_in_row_replace_nth_le.
      exact Hle.
    + apply Nat.add_le_mono_l.
      apply IH.
      exact Hle.
Qed.

(** Position-based cell replacement cannot increase the hidden-safe count
    when the replacement tile contributes no more hidden-safe mass. *)
Lemma hidden_safe_total_set_tile_pos_le :
  forall b p t,
    hidden_safe_weight t <= hidden_safe_weight (get_tile_pos p b) ->
    hidden_safe_total (set_tile_pos p t b) <= hidden_safe_total b.
Proof.
  intros b [row col] t Hle.
  unfold set_tile_pos, get_tile_pos.
  apply hidden_safe_total_set_tile_le.
  exact Hle.
Qed.

(** Revealing a tile and clearing its flag never increases its hidden-safe contribution. *)
Lemma hidden_safe_weight_reveal_clear_flag_le :
  forall t,
    hidden_safe_weight (tile_reveal_clear_flag t) <= hidden_safe_weight t.
Proof.
  intros [m r f a].
  unfold hidden_safe_weight, tile_reveal_clear_flag.
  simpl.
  destruct m, r; simpl; lia.
Qed.

(** Revealing and clearing a single tile cannot increase the board's hidden-safe count. *)
Lemma hidden_safe_total_reveal_clear_flag_le :
  forall b p,
    hidden_safe_total (set_tile_pos p (tile_reveal_clear_flag (get_tile_pos p b)) b) <=
    hidden_safe_total b.
Proof.
  intros b p.
  apply hidden_safe_total_set_tile_pos_le.
  apply hidden_safe_weight_reveal_clear_flag_le.
Qed.

(** The recursive reveal flood-fill cannot increase the hidden-safe count. *)
Lemma reveal_region_hidden_safe_total_monotone :
  forall fuel todo b,
    hidden_safe_total (reveal_region fuel todo b) <= hidden_safe_total b.
Proof.
  induction fuel as [|fuel IH]; intros todo b; simpl.
  - lia.
  - destruct todo as [|p rest].
    + lia.
    + remember (get_tile_pos p b) as t.
      destruct (tile_revealed t || tile_flagged t || tile_mine t) eqn:Hstop.
      * apply IH.
      * rewrite Heqt.
        eapply Nat.le_trans.
        2: apply hidden_safe_total_reveal_clear_flag_le.
        apply IH.
Qed.

(** Generated boards are well formed whenever the cursor position is in bounds. *)
Lemma generate_board_wf :
  forall seed0 safe,
    position_in_bounds safe ->
    well_formed_board (generate_board seed0 safe).
Proof.
  intros seed0 safe Hsafe.
  unfold generate_board.
  apply annotate_board_wf.
  apply place_mines_wf.
  apply blank_board_wf.
Qed.

(** The board that [reveal_at_cursor] conceptually starts from before it mutates visibility. *)
Definition reveal_source_board (gs : game_state) : list (list tile) :=
  match game_phase gs with
  | Playing =>
      if waiting_for_first_reveal gs
      then generate_board (seed gs) (cursor gs)
      else board gs
  | _ => board gs
  end.

(** Rebuilding a state with a well-formed board keeps the overall state well formed. *)
Lemma state_with_board_wf :
  forall gs b,
    well_formed_board b ->
    position_in_bounds (cursor gs) ->
    well_formed_state (state_with_board gs b).
Proof.
  intros gs b Hwf Hcur.
  unfold well_formed_state.
  split; assumption.
Qed.

(** The reveal flood-fill preserves board shape when started from a well-formed board
    and an in-bounds worklist. *)
Lemma reveal_region_wf :
  forall fuel todo b,
    well_formed_board b ->
    Forall position_in_bounds todo ->
    well_formed_board (reveal_region fuel todo b).
Proof.
  induction fuel as [|fuel IH]; intros todo b Hwf Htodo; simpl.
  - exact Hwf.
  - destruct todo as [|p rest].
    + exact Hwf.
    + inversion Htodo as [|p' rest' Hp Hrest]; subst.
      remember (get_tile_pos p b) as t.
      destruct (tile_revealed t || tile_flagged t || tile_mine t) eqn:Hstop.
      * apply IH; assumption.
      * assert (Hwf1 : well_formed_board
            (set_tile_pos p (tile_reveal_clear_flag t) b)).
        { apply set_tile_pos_wf; assumption. }
        assert (Htodo' : Forall position_in_bounds
            (if Nat.eqb (tile_adjacent t) 0 then neighbors p ++ rest else rest)).
        {
          destruct (Nat.eqb (tile_adjacent t) 0); auto.
          apply Forall_app.
          split.
          - apply neighbors_in_bounds. exact Hp.
          - exact Hrest.
        }
        apply IH; assumption.
Qed.

(** Flag toggling preserves board shape and cursor bounds. *)
Lemma toggle_flag_at_cursor_wf :
  forall gs,
    well_formed_state gs ->
    well_formed_state (toggle_flag_at_cursor gs).
Proof.
  intros gs [Hwf Hcur].
  unfold toggle_flag_at_cursor, well_formed_state.
  destruct (game_phase gs); simpl; try (split; assumption).
  remember (get_tile_pos (cursor gs) (board gs)) as t.
  destruct (tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)); simpl.
  - split; assumption.
  - split.
    + apply set_tile_pos_wf; assumption.
    + exact Hcur.
Qed.

(** If the chosen tile is already blocked for reveal, the helper leaves the board unchanged. *)
Lemma reveal_playing_result_board_wf_stop :
  forall gs board0,
    tile_flagged (reveal_playing_source_tile gs board0) ||
    tile_revealed (reveal_playing_source_tile gs board0) = true ->
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    well_formed_board (reveal_playing_result_board gs board0).
Proof.
  intros gs board0 Hstop Hcur Hwf0.
  unfold reveal_playing_result_board.
  rewrite Hstop.
  exact Hwf0.
Qed.

(** If the chosen tile is a mine, the helper only updates that single in-bounds cell. *)
Lemma reveal_playing_result_board_wf_mine :
  forall gs board0,
    tile_flagged (reveal_playing_source_tile gs board0) ||
    tile_revealed (reveal_playing_source_tile gs board0) = false ->
    tile_mine (reveal_playing_source_tile gs board0) = true ->
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    well_formed_board (reveal_playing_result_board gs board0).
Proof.
  intros gs board0 Hstop Hmine Hcur Hwf0.
  unfold reveal_playing_result_board.
  rewrite Hstop, Hmine.
  apply set_tile_pos_wf; assumption.
Qed.

(** If the chosen tile is a safe unrevealed tile, the helper delegates to the flood-fill reveal. *)
Lemma reveal_playing_result_board_wf_safe :
  forall gs board0,
    tile_flagged (reveal_playing_source_tile gs board0) ||
    tile_revealed (reveal_playing_source_tile gs board0) = false ->
    tile_mine (reveal_playing_source_tile gs board0) = false ->
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    well_formed_board (reveal_playing_result_board gs board0).
Proof.
  intros gs board0 Hstop Hmine Hcur Hwf0.
  unfold reveal_playing_result_board.
  rewrite Hstop, Hmine.
  apply reveal_region_wf.
  - exact Hwf0.
  - constructor; [exact Hcur|constructor].
Qed.

(** Starting a reveal from any well-formed candidate board preserves board shape. *)
Lemma reveal_playing_result_board_wf :
  forall gs board0,
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    well_formed_board (reveal_playing_result_board gs board0).
Proof.
  intros gs board0 Hcur Hwf0.
  remember (tile_flagged (reveal_playing_source_tile gs board0) ||
            tile_revealed (reveal_playing_source_tile gs board0)) as stop eqn:Hstop.
  destruct stop.
  - symmetry in Hstop.
    apply reveal_playing_result_board_wf_stop; assumption.
  - symmetry in Hstop.
    remember (tile_mine (reveal_playing_source_tile gs board0)) as mine eqn:Hmine.
    destruct mine.
    + symmetry in Hmine.
      apply reveal_playing_result_board_wf_mine; assumption.
    + symmetry in Hmine.
      apply reveal_playing_result_board_wf_safe; assumption.
Qed.

(** Starting a reveal from any well-formed candidate board preserves board shape
    and cursor bounds. *)
Lemma reveal_playing_from_board_wf :
  forall gs board0,
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    well_formed_state (reveal_playing_from_board gs board0).
Proof.
  intros gs board0 Hcur Hwf0.
  unfold well_formed_state.
  split.
  - apply reveal_playing_result_board_wf; assumption.
  - exact Hcur.
Qed.

(** Revealing at the cursor preserves board shape and cursor bounds. *)
Lemma reveal_at_cursor_wf :
  forall gs,
    well_formed_state gs ->
    well_formed_state (reveal_at_cursor gs).
Proof.
  intros [b cur ph wait s] [Hwf Hcur].
  unfold reveal_at_cursor; simpl.
  destruct ph; simpl; try (split; assumption).
  destruct wait.
  - apply reveal_playing_from_board_wf.
    + exact Hcur.
    + apply generate_board_wf. exact Hcur.
  - apply reveal_playing_from_board_wf.
    + exact Hcur.
    + exact Hwf.
Qed.

(** The playing-phase result board preserves mine placement relative to its source board. *)
Lemma reveal_playing_result_board_preserves_mine_layout :
  forall gs board0,
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    same_mine_layout (reveal_playing_result_board gs board0) board0.
Proof.
  intros gs board0 Hcur Hwf0 p Hp.
  remember (tile_flagged (reveal_playing_source_tile gs board0) ||
            tile_revealed (reveal_playing_source_tile gs board0)) as stop eqn:Hstop.
  destruct stop.
  - unfold reveal_playing_result_board.
    symmetry in Hstop.
    rewrite Hstop.
    reflexivity.
  - symmetry in Hstop.
    remember (tile_mine (reveal_playing_source_tile gs board0)) as mine eqn:Hmine.
    destruct mine.
    + symmetry in Hmine.
      unfold reveal_playing_result_board.
      rewrite Hstop, Hmine.
      assert (Hsame : same_mine_layout
        (set_tile_pos (cursor gs)
           (tile_reveal_clear_flag (reveal_playing_source_tile gs board0)) board0)
        board0).
      { apply set_tile_pos_preserves_mine_layout.
        - exact Hwf0.
        - exact Hcur.
        - unfold reveal_playing_source_tile.
          apply tile_reveal_clear_flag_preserves_mine. }
      exact (Hsame p Hp).
    + symmetry in Hmine.
      unfold reveal_playing_result_board.
      rewrite Hstop, Hmine.
      assert (Hsame : same_mine_layout
        (reveal_region (total_cells * total_cells) [cursor gs] board0) board0).
      { apply reveal_region_preserves_mine_layout.
        - exact Hwf0.
        - constructor; [exact Hcur|constructor]. }
      exact (Hsame p Hp).
Qed.

(** The playing-phase result board cannot increase the hidden-safe-cell count. *)
Lemma reveal_playing_result_board_hidden_safe_total_monotone :
  forall gs board0,
    hidden_safe_total (reveal_playing_result_board gs board0) <= hidden_safe_total board0.
Proof.
  intros gs board0.
  remember (tile_flagged (reveal_playing_source_tile gs board0) ||
            tile_revealed (reveal_playing_source_tile gs board0)) as stop eqn:Hstop.
  destruct stop.
  - unfold reveal_playing_result_board.
    symmetry in Hstop.
    rewrite Hstop.
    lia.
  - symmetry in Hstop.
    remember (tile_mine (reveal_playing_source_tile gs board0)) as mine eqn:Hmine.
    destruct mine.
    + symmetry in Hmine.
      unfold reveal_playing_result_board.
      rewrite Hstop, Hmine.
      unfold reveal_playing_source_tile.
      apply hidden_safe_total_reveal_clear_flag_le.
    + symmetry in Hmine.
      unfold reveal_playing_result_board.
      rewrite Hstop, Hmine.
      apply reveal_region_hidden_safe_total_monotone.
Qed.

(** If the playing-phase result ends in [Won], the resulting board has no hidden safe cells. *)
Lemma reveal_playing_result_phase_won_hidden_safe_zero :
  forall gs board0,
    reveal_playing_result_phase gs board0 = Won ->
    hidden_safe_total (reveal_playing_result_board gs board0) = 0.
Proof.
  intros gs board0 Hwon.
  unfold reveal_playing_result_phase in Hwon.
  remember (tile_flagged (reveal_playing_source_tile gs board0) ||
            tile_revealed (reveal_playing_source_tile gs board0)) as stop eqn:Hstop.
  destruct stop; try discriminate.
  remember (tile_mine (reveal_playing_source_tile gs board0)) as mine eqn:Hmine.
  destruct mine; try discriminate.
  remember (Nat.eqb (hidden_safe_total (reveal_playing_result_board gs board0)) 0) as done eqn:Hdone.
  destruct done; inversion Hwon; subst.
  apply Nat.eqb_eq.
  symmetry. exact Hdone.
Qed.

(** If the playing-phase result ends in [Lost], the cursor cell is a revealed mine. *)
Lemma reveal_playing_result_phase_lost_reveals_mine :
  forall gs board0,
    position_in_bounds (cursor gs) ->
    well_formed_board board0 ->
    reveal_playing_result_phase gs board0 = Lost ->
    exists p,
      position_in_bounds p /\
      tile_mine (get_tile_pos p (reveal_playing_result_board gs board0)) = true /\
      tile_revealed (get_tile_pos p (reveal_playing_result_board gs board0)) = true.
Proof.
  intros gs board0 Hcur Hwf0 Hlost.
  unfold reveal_playing_result_phase in Hlost.
  remember (tile_flagged (reveal_playing_source_tile gs board0) ||
            tile_revealed (reveal_playing_source_tile gs board0)) as stop eqn:Hstop.
  destruct stop; try discriminate.
  remember (tile_mine (reveal_playing_source_tile gs board0)) as mine eqn:Hmine.
  destruct mine.
  - exists (cursor gs).
    split; [exact Hcur|].
    split.
    + unfold reveal_playing_result_board.
      symmetry in Hstop, Hmine.
      rewrite Hstop, Hmine.
      rewrite (get_tile_pos_set_tile_pos_same board0 (cursor gs)
                 (tile_reveal_clear_flag (reveal_playing_source_tile gs board0))).
      2: exact Hwf0.
      2: exact Hcur.
      unfold reveal_playing_source_tile.
      rewrite <- Hmine.
      apply tile_reveal_clear_flag_preserves_mine.
    + unfold reveal_playing_result_board.
      symmetry in Hstop, Hmine.
      rewrite Hstop, Hmine.
      rewrite (get_tile_pos_set_tile_pos_same board0 (cursor gs)
                 (tile_reveal_clear_flag (reveal_playing_source_tile gs board0))).
      2: exact Hwf0.
      2: exact Hcur.
      unfold reveal_playing_source_tile.
      destruct (get_tile_pos (cursor gs) board0).
      reflexivity.
  - remember (Nat.eqb (hidden_safe_total (reveal_playing_result_board gs board0)) 0) as done eqn:Hdone.
    destruct done; discriminate Hlost.
Qed.

(** Revealing at the cursor preserves mine placement relative to the board
    that the reveal logic actually starts from. *)
Theorem reveal_at_cursor_preserves_mine_layout_sketch :
  forall gs,
    well_formed_state gs ->
    same_mine_layout (board (reveal_at_cursor gs)) (reveal_source_board gs).
Proof.
  intros gs [Hwf Hcur].
  unfold reveal_at_cursor, reveal_source_board.
  destruct (game_phase gs); simpl.
  - destruct (waiting_for_first_reveal gs).
    + apply reveal_playing_result_board_preserves_mine_layout.
      * exact Hcur.
      * apply generate_board_wf. exact Hcur.
    + apply reveal_playing_result_board_preserves_mine_layout.
      * exact Hcur.
      * exact Hwf.
  - apply same_mine_layout_refl.
  - apply same_mine_layout_refl.
Qed.

(** Revealing at the cursor cannot increase the hidden-safe count relative to
    the board that the reveal logic actually starts from. *)
Theorem reveal_at_cursor_hidden_safe_total_monotone_sketch :
  forall gs,
    well_formed_state gs ->
    hidden_safe_total (board (reveal_at_cursor gs)) <=
    hidden_safe_total (reveal_source_board gs).
Proof.
  intros gs [Hwf Hcur].
  unfold reveal_at_cursor, reveal_source_board.
  destruct (game_phase gs); simpl.
  - destruct (waiting_for_first_reveal gs).
    + apply reveal_playing_result_board_hidden_safe_total_monotone.
    + apply reveal_playing_result_board_hidden_safe_total_monotone.
  - lia.
  - lia.
Qed.

(** If a reveal from a playing state ends in [Won], then no hidden safe cells remain. *)
Theorem reveal_at_cursor_win_condition_sketch :
  forall gs,
    well_formed_state gs ->
    game_phase gs = Playing ->
    game_phase (reveal_at_cursor gs) = Won ->
    hidden_safe_total (board (reveal_at_cursor gs)) = 0.
Proof.
  intros gs Hwf Hplaying Hwon.
  unfold reveal_at_cursor in *.
  rewrite Hplaying in Hwon |- *.
  destruct (waiting_for_first_reveal gs).
  - simpl in Hwon |- *.
    apply reveal_playing_result_phase_won_hidden_safe_zero in Hwon.
    exact Hwon.
  - simpl in Hwon |- *.
    apply reveal_playing_result_phase_won_hidden_safe_zero in Hwon.
    exact Hwon.
Qed.

(** If a reveal from a playing state ends in [Lost], then some mine is both present and revealed. *)
Lemma reveal_at_cursor_lost_reveals_mine :
  forall gs,
    well_formed_state gs ->
    game_phase gs = Playing ->
    game_phase (reveal_at_cursor gs) = Lost ->
    exists p,
      position_in_bounds p /\
      tile_mine (get_tile_pos p (board (reveal_at_cursor gs))) = true /\
      tile_revealed (get_tile_pos p (board (reveal_at_cursor gs))) = true.
Proof.
  intros gs [Hwf Hcur] Hplaying Hlost.
  unfold reveal_at_cursor in *.
  rewrite Hplaying in Hlost |- *.
  destruct (waiting_for_first_reveal gs).
  - simpl in Hlost |- *.
    eapply reveal_playing_result_phase_lost_reveals_mine.
    + exact Hcur.
    + apply generate_board_wf. exact Hcur.
    + exact Hlost.
  - simpl in Hlost |- *.
    eapply reveal_playing_result_phase_lost_reveals_mine.
    + exact Hcur.
    + exact Hwf.
    + exact Hlost.
Qed.

(** A game state satisfies the end-to-end outcome specification when wins leave
    no hidden safe cells and losses expose a revealed mine. *)
Definition outcome_spec (gs : game_state) : Prop :=
  (game_phase gs = Won -> hidden_safe_total (board gs) = 0) /\
  (game_phase gs = Lost -> exists p,
      position_in_bounds p /\
      tile_mine (get_tile_pos p (board gs)) = true /\
      tile_revealed (get_tile_pos p (board gs)) = true).

(** The initial state trivially satisfies the outcome specification because it is still playing. *)
Lemma initial_state_outcome_spec :
  forall seed0,
    outcome_spec (initial_state seed0).
Proof.
  intros seed0.
  split; intros Hphase; discriminate.
Qed.

(** Every pure gameplay step preserves well-formedness and the outcome specification. *)
Lemma pure_game_step_preserves_wf_outcome :
  forall gs1 gs2,
    pure_game_step gs1 gs2 ->
    well_formed_state gs1 ->
    outcome_spec gs1 ->
    well_formed_state gs2 /\ outcome_spec gs2.
Proof.
  intros gs1 gs2 Hstep Hwf [Hwon1 Hlost1].
  destruct Hstep.
  - split.
    + apply reveal_at_cursor_wf. exact Hwf.
    + split.
      * intros Hwon2.
        destruct (game_phase gs) eqn:Hphase.
        -- eapply reveal_at_cursor_win_condition_sketch; eauto.
        -- rewrite reveal_at_cursor_terminal_noop in Hwon2 by (left; exact Hphase).
           rewrite reveal_at_cursor_terminal_noop by (left; exact Hphase).
           apply Hwon1. reflexivity.
        -- rewrite reveal_at_cursor_terminal_noop in Hwon2 by (right; exact Hphase).
           rewrite Hphase in Hwon2.
           discriminate Hwon2.
      * intros Hlost2.
        destruct (game_phase gs) eqn:Hphase.
        -- eapply reveal_at_cursor_lost_reveals_mine; eauto.
        -- rewrite reveal_at_cursor_terminal_noop in Hlost2 by (left; exact Hphase).
           rewrite Hphase in Hlost2.
           discriminate Hlost2.
        -- rewrite reveal_at_cursor_terminal_noop in Hlost2 by (right; exact Hphase).
           rewrite reveal_at_cursor_terminal_noop by (right; exact Hphase).
           apply Hlost1. reflexivity.
  - split.
    + apply toggle_flag_at_cursor_wf. exact Hwf.
    + split.
      * intros Hwon2.
        destruct (game_phase gs) eqn:Hphase.
        -- unfold toggle_flag_at_cursor in Hwon2.
           rewrite Hphase in Hwon2.
           remember (get_tile_pos (cursor gs) (board gs)) as t.
           destruct (tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)); simpl in Hwon2.
           ++ rewrite Hphase in Hwon2. discriminate Hwon2.
           ++ discriminate Hwon2.
        -- rewrite toggle_flag_at_cursor_terminal_noop in Hwon2 by (left; exact Hphase).
           rewrite toggle_flag_at_cursor_terminal_noop by (left; exact Hphase).
           apply Hwon1. reflexivity.
        -- rewrite toggle_flag_at_cursor_terminal_noop in Hwon2 by (right; exact Hphase).
           rewrite Hphase in Hwon2.
           discriminate Hwon2.
      * intros Hlost2.
        destruct (game_phase gs) eqn:Hphase.
        -- unfold toggle_flag_at_cursor in Hlost2.
           rewrite Hphase in Hlost2.
           remember (get_tile_pos (cursor gs) (board gs)) as t.
           destruct (tile_revealed t || (waiting_for_first_reveal gs && tile_revealed t)); simpl in Hlost2.
           ++ rewrite Hphase in Hlost2. discriminate Hlost2.
           ++ discriminate Hlost2.
        -- rewrite toggle_flag_at_cursor_terminal_noop in Hlost2 by (left; exact Hphase).
           rewrite Hphase in Hlost2.
           discriminate Hlost2.
        -- rewrite toggle_flag_at_cursor_terminal_noop in Hlost2 by (right; exact Hphase).
           rewrite toggle_flag_at_cursor_terminal_noop by (right; exact Hphase).
           apply Hlost1. reflexivity.
  - split.
    + apply restart_state_wf.
    + split; intros Hphase; discriminate.
Qed.

(** Whole pure gameplay traces preserve well-formedness and the outcome specification. *)
Lemma pure_game_trace_preserves_wf_outcome :
  forall gs1 gs2,
    pure_game_trace gs1 gs2 ->
    well_formed_state gs1 ->
    outcome_spec gs1 ->
    well_formed_state gs2 /\ outcome_spec gs2.
Proof.
  intros gs1 gs2 Htrace.
  induction Htrace; intros Hwf Hspec.
  - split; assumption.
  - destruct (pure_game_step_preserves_wf_outcome _ _ H Hwf Hspec) as [Hwf2 Hspec2].
    apply IHHtrace; assumption.
Qed.

(** Whole-trace gameplay specification over pure steps starting from the initial state. *)
Theorem pure_game_trace_outcome_spec_sketch :
  forall seed0 gs,
    pure_game_trace (initial_state seed0) gs ->
    outcome_spec gs.
Proof.
  intros seed0 gs Htrace.
  pose proof (pure_game_trace_preserves_wf_outcome
                (initial_state seed0) gs Htrace
                (initial_state_wf seed0)
                (initial_state_outcome_spec seed0)) as [_ Hspec].
  exact Hspec.
Qed.
