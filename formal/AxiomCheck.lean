import EndgameChess

/-! Axiom audit for EC-C001. Run: `lake env lean AxiomCheck.lean`. -/

#print axioms EndgameChess.KK.dead_of_admissible
#print axioms EndgameChess.KK.dead_of_last_move_legal
#print axioms EndgameChess.KK.admissible_of_last_move_legal
#print axioms EndgameChess.KK.attack_iff_dInf_one
#print axioms EndgameChess.KK.not_inCheck_of_admissible
#print axioms EndgameChess.KK.admissible_of_legal_step
#print axioms EndgameChess.KK.admissible_of_reach
#print axioms EndgameChess.KK.not_checkmate_of_reach
#print axioms EndgameChess.KK.legalKK_iff_prose
#print axioms EndgameChess.KK.exists_legal_move_of_admissible
#print axioms EndgameChess.KK.checkmate_satisfiable
#print axioms EndgameChess.KK.reach_nontrivial

#check @EndgameChess.KK.dead_of_admissible
#check @EndgameChess.KK.dead_of_last_move_legal

/-! EC-C002 (K+B vs K) -/
#print axioms EndgameChess.KBK.dead_of_LKBK
#print axioms EndgameChess.KBK.dead_of_step
#print axioms EndgameChess.KBK.dead_of_closed
#print axioms EndgameChess.KBK.LKBK_of_step
#print axioms EndgameChess.KBK.weak_has_move_of_inCheck
#print axioms EndgameChess.KBK.colour_of_bishopAttacks
#print axioms EndgameChess.KBK.colour_orth_neighbour
#print axioms EndgameChess.KBK.kings_apart_of_LKBK
#print axioms EndgameChess.KBK.strong_not_inCheck_of_LKBK
#print axioms EndgameChess.KBK.closed_of_step
#print axioms EndgameChess.KBK.closed_of_reach
#print axioms EndgameChess.KBK.not_mated_of_closed
#print axioms EndgameChess.KBK.admissible_of_capture
#print axioms EndgameChess.KBK.bishop_check_exists
#print axioms EndgameChess.KBK.stalemate_exists
#print axioms EndgameChess.KBK.mated_satisfiable

#check @EndgameChess.KBK.dead_of_LKBK
#check @EndgameChess.KBK.dead_of_step

/-! EC-C004 rules kernel K1 (S007) -/
#print axioms EndgameChess.Rules.mem_allSquares
#print axioms EndgameChess.Rules.initial_wellFormed
#print axioms EndgameChess.Rules.mem_legalMoves
#print axioms EndgameChess.Rules.mem_legalPositions
#print axioms EndgameChess.Rules.not_inCheck_after_legal
#print axioms EndgameChess.Rules.legal_mover_safe
#print axioms EndgameChess.Rules.initial_legal_count
#print axioms EndgameChess.Rules.enPassant_legal
#print axioms EndgameChess.Rules.enPassant_expired
#print axioms EndgameChess.Rules.enPassant_exposing_king_illegal
#print axioms EndgameChess.Rules.promotion_rules
#print axioms EndgameChess.Rules.castling_legal
#print axioms EndgameChess.Rules.castling_through_check_illegal
#print axioms EndgameChess.Rules.castling_without_right_illegal
#print axioms EndgameChess.Rules.pinned_piece_cannot_move
#print axioms EndgameChess.Rules.king_never_captured
#print axioms EndgameChess.Rules.castling_queenside_b1_attacked_legal
#print axioms EndgameChess.Rules.castling_out_of_check_illegal

/-! EC-C004 rules kernel K2 (S008): agreement with the frozen models -/
#print axioms EndgameChess.Rules.dead_transfer
#print axioms EndgameChess.Rules.legal_ofKK_iff
#print axioms EndgameChess.Rules.legalKK_iff_kernel
#print axioms EndgameChess.Rules.deadK_ofKK_iff
#print axioms EndgameChess.Rules.kernel_dead_KK
#print axioms EndgameChess.Rules.isBetween_iff_between
#print axioms EndgameChess.Rules.bishop_kbk
#print axioms EndgameChess.Rules.attacked_kbk
#print axioms EndgameChess.Rules.inCheck_weak
#print axioms EndgameChess.Rules.inCheck_strong
#print axioms EndgameChess.Rules.legal_ofKBK_iff
#print axioms EndgameChess.Rules.deadK_embPos_iff
#print axioms EndgameChess.Rules.deadK_ofKBK_iff
#print axioms EndgameChess.Rules.kernel_dead_KBK

#check @EndgameChess.Rules.legal_ofKK_iff
#check @EndgameChess.Rules.legal_ofKBK_iff
#check @EndgameChess.Rules.deadK_ofKK_iff
#check @EndgameChess.Rules.deadK_ofKBK_iff
#check @EndgameChess.Rules.kernel_dead_KK
#check @EndgameChess.Rules.kernel_dead_KBK
#print axioms EndgameChess.Rules.kernel_kk_has_move
#print axioms EndgameChess.Rules.kernel_kbk_check_has_move

/-! EC-C004 rules kernel K3 (S009): flags, reachability, Art. 5.2.2 rule -/
#print axioms EndgameChess.Rules.deadK_normFlags_iff
#print axioms EndgameChess.Rules.legal_normFlags_iff
#print axioms EndgameChess.Rules.isPseudo_normFlags
#print axioms EndgameChess.Rules.play_nrp
#print axioms EndgameChess.Rules.nrp_of_legal
#print axioms EndgameChess.Rules.dead_of_legal_into_KK
#print axioms EndgameChess.Rules.dead_of_legal_into_KBK
#print axioms EndgameChess.Rules.arisen_KK_dead
#print axioms EndgameChess.Rules.arisen_KBK_dead
#print axioms EndgameChess.Rules.initial_not_KK
#print axioms EndgameChess.Rules.initial_not_KBK
#print axioms EndgameChess.Rules.capture_into_KK_example
#print axioms EndgameChess.Rules.kk_drawn_by_rule
#print axioms EndgameChess.Rules.kbk_drawn_by_rule

#check @EndgameChess.Rules.dead_of_legal_into_KK
#check @EndgameChess.Rules.dead_of_legal_into_KBK
#check @EndgameChess.Rules.arisen_KK_dead
#check @EndgameChess.Rules.arisen_KBK_dead
#print EndgameChess.Rules.Rule5_2_2
#check @EndgameChess.Rules.kk_drawn_by_rule
#check @EndgameChess.Rules.kbk_drawn_by_rule

/-! EC-C003 (K+N vs K over the rules kernel, S012) -/
#print axioms EndgameChess.Rules.dead_of_legal_into_KNK
#print axioms EndgameChess.Rules.arisen_KNK_dead
#print axioms EndgameChess.Rules.knk_drawn_by_rule
#print axioms EndgameChess.Rules.initial_not_KNK
#print axioms EndgameChess.Rules.weak_has_move
#print axioms EndgameChess.Rules.escape_square
#print axioms EndgameChess.Rules.knight_not_orth
#print axioms EndgameChess.Rules.ne_of_knight_adj
#print axioms EndgameChess.Rules.kings_apart_of_legal
#print axioms EndgameChess.Rules.strong_not_inCheck
#print axioms EndgameChess.Rules.step_closed
#print axioms EndgameChess.Rules.reach_cases
#print axioms EndgameChess.Rules.not_mated_KNK
#print axioms EndgameChess.Rules.inCheck_weak_knk
#print axioms EndgameChess.Rules.inCheck_strong_knk
#print axioms EndgameChess.Rules.knight_check_example
#print axioms EndgameChess.Rules.knk_stalemate_example
#print axioms EndgameChess.Rules.knight_capture_example

#check @EndgameChess.Rules.dead_of_legal_into_KNK
#check @EndgameChess.Rules.arisen_KNK_dead
#check @EndgameChess.Rules.knk_drawn_by_rule

/-! EC-C007 (dead K+R vs K: forced capture / stalemate, over the rules kernel, S015) -/
#print axioms EndgameChess.Rules.reachK_head
#print axioms EndgameChess.Rules.dead_of_succ_dead
#print axioms EndgameChess.Rules.dead_of_succ_KK
#print axioms EndgameChess.Rules.krk_dead_of_forced_capture
#print axioms EndgameChess.Rules.krk_forced_capture_drawn_by_rule
#print axioms EndgameChess.Rules.legal_of_legalMoves_eq
#print axioms EndgameChess.Rules.krk_forced_capture_example
#print axioms EndgameChess.Rules.krk_stalemate_dead_example
#print axioms EndgameChess.Rules.krk_live_example

#check @EndgameChess.Rules.dead_of_succ_KK
#check @EndgameChess.Rules.krk_dead_of_forced_capture
#check @EndgameChess.Rules.krk_forced_capture_drawn_by_rule

/-! EC-C008 Lean, part 1 (S021): infrastructure (Rules/KRKLive/Basic) -/
#print axioms EndgameChess.Rules.lineGeom_iff
#print axioms EndgameChess.Rules.isBetween_iff_onSeg
#print axioms EndgameChess.Rules.pathClear_iff
#print axioms EndgameChess.Rules.rook_attacks_krk
#print axioms EndgameChess.Rules.attacked_krk
#print axioms EndgameChess.Rules.inCheck_weak_krk
#print axioms EndgameChess.Rules.inCheck_strong_krk
#print axioms EndgameChess.Rules.play_board_simple
#print axioms EndgameChess.Rules.legal_of_pseudo
#print axioms EndgameChess.Rules.winM_of_step
#print axioms EndgameChess.Rules.step_sound
#print axioms EndgameChess.Rules.mate_sound
#print axioms EndgameChess.Rules.chain_sound
#print axioms EndgameChess.Rules.not_deadK_of_winM
#print axioms EndgameChess.Rules.step_map
#print axioms EndgameChess.Rules.mate_map
#print axioms EndgameChess.Rules.winM_map
#print axioms EndgameChess.Rules.winM_of_sym
#print axioms EndgameChess.Rules.exists_sym_normal

/-! EC-C008 Lean, part 1 (S021): end-game half (Rules/KRKLive/Endgame) -/
#print axioms EndgameChess.Rules.tempo_step
#print axioms EndgameChess.Rules.lone_step_region
#print axioms EndgameChess.Rules.krk_lemmaM
#print axioms EndgameChess.Rules.krk_lemmaE_lone
#print axioms EndgameChess.Rules.krk_lemmaE
#print axioms EndgameChess.Rules.Conn.symm
#print axioms EndgameChess.Rules.Conn.trans
#print axioms EndgameChess.Rules.rect_minus_box_conn
#print axioms EndgameChess.Rules.krk_conn_region
#print axioms EndgameChess.Rules.krk_lemmaW
#print axioms EndgameChess.Rules.krk_lemmaS
#print axioms EndgameChess.Rules.krk_settled_live
#print axioms EndgameChess.Rules.krkM_mate_example
#print axioms EndgameChess.Rules.krkM_example
#print axioms EndgameChess.Rules.krkS_rank8_example
#print axioms EndgameChess.Rules.krkS_g7_example

#check @EndgameChess.Rules.not_deadK_of_winM
#check @EndgameChess.Rules.krk_lemmaS
#check @EndgameChess.Rules.krk_settled_live


/-! EC-C008 Lean, part 2 (S022): replies RL-h, RL-f (Rules/KRKLive/Reply) -/
#print axioms EndgameChess.Rules.krk_RLh
#print axioms EndgameChess.Rules.krk_RLf

/-! EC-C008 Lean, part 2 (S022): P1 (Rules/KRKLive/Relocation) -/
#print axioms EndgameChess.Rules.rookInv_of_free
#print axioms EndgameChess.Rules.onSeg_trans
#print axioms EndgameChess.Rules.shield_of_line
#print axioms EndgameChess.Rules.rook_move_ok
#print axioms EndgameChess.Rules.after_rook
#print axioms EndgameChess.Rules.krk_home
#print axioms EndgameChess.Rules.krk_hfile
#print axioms EndgameChess.Rules.krk_rankToH
#print axioms EndgameChess.Rules.krk_fs
#print axioms EndgameChess.Rules.krk_P1

/-! EC-C008 Lean, part 2 (S022): main theorems (Rules/KRKLive/Main) -/
#print axioms EndgameChess.Rules.krk_live_of_not_check
#print axioms EndgameChess.Rules.krk_strong_to_move_live
#print axioms EndgameChess.Rules.reachK_cons
#print axioms EndgameChess.Rules.lone_move_cases
#print axioms EndgameChess.Rules.krk_dead_iff
#print axioms EndgameChess.Rules.initial_not_KRK
#print axioms EndgameChess.Rules.arisen_krk_strong_live
#print axioms EndgameChess.Rules.krk_drawn_by_rule_iff
#print axioms EndgameChess.Rules.rlh_exception_example
#print axioms EndgameChess.Rules.fsF2_example
#print axioms EndgameChess.Rules.krk_strong_live_example

#check @EndgameChess.Rules.krk_strong_to_move_live
#check @EndgameChess.Rules.krk_dead_iff
#check @EndgameChess.Rules.arisen_krk_strong_live
#check @EndgameChess.Rules.krk_drawn_by_rule_iff
#check @EndgameChess.Rules.krk_live_of_not_check

/-! S024: forcing semantics (EC-C009), all-replies confinement (EC-C010), witnesses. -/
#print axioms EndgameChess.Rules.mateWithin_mono_step
#print axioms EndgameChess.Rules.mateWithin_mono
#print axioms EndgameChess.Rules.mateWithin_sound
#print axioms EndgameChess.Rules.forceMate_not_dead
#print axioms EndgameChess.Rules.forceMate_of_goal
#print axioms EndgameChess.Rules.forceMate_no_moves_iff
#print axioms EndgameChess.Rules.dead_reply_not_forceMate
#print axioms EndgameChess.Rules.stalemate_not_forceMate
#print axioms EndgameChess.Rules.forceMate_choose
#print axioms EndgameChess.Rules.forceMate_defend
#print axioms EndgameChess.Rules.krk_protected_reply
#print axioms EndgameChess.Rules.rook_rank_barrier
#print axioms EndgameChess.Rules.protected_rank_raise_unprotected
#print axioms EndgameChess.Rules.krk_protected_rank_reply
#print axioms EndgameChess.Rules.krk_optional_capture_counterexample
#print axioms EndgameChess.Rules.optional_capture_holds
#print axioms EndgameChess.Rules.krk_force_mate_in_one_example
#print axioms EndgameChess.Rules.protected_rank_stalemate_example
#print axioms EndgameChess.Rules.blocked_rank_counterexample
#check @EndgameChess.Rules.mateWithin_sound
#check @EndgameChess.Rules.forceMate_defend
#check @EndgameChess.Rules.dead_reply_not_forceMate
#check @EndgameChess.Rules.krk_protected_rank_reply

/-! S026: distant safety and all-defences checking progress. -/
#print axioms EndgameChess.Rules.krk_safe_reply
#print axioms EndgameChess.Rules.krk_safe_rank_reply
#print axioms EndgameChess.Rules.krk_safe_weak_live
#print axioms EndgameChess.Rules.rank_sees_of_below
#print axioms EndgameChess.Rules.opposition_check_step
#print axioms EndgameChess.Rules.opposition_edge_mate
#print axioms EndgameChess.Rules.opposition_reply_up
#print axioms EndgameChess.Rules.opposition_up_reply_exists
#print axioms EndgameChess.Rules.krk_opposition_check
#print axioms EndgameChess.Rules.krk_opposition_edge_force
#print axioms EndgameChess.Rules.follow_horizontal_reply
#print axioms EndgameChess.Rules.krk_follow_check
#print axioms EndgameChess.Rules.krk_opposition_four_ply
#print axioms EndgameChess.Rules.opposition_edge_force_example
#print axioms EndgameChess.Rules.two_file_margin_capture
#print axioms EndgameChess.Rules.three_file_margin_hanging
#print axioms EndgameChess.Rules.phase_need_not_restore_opposition

#check @EndgameChess.Rules.krk_safe_reply
#check @EndgameChess.Rules.krk_safe_weak_live
#check @EndgameChess.Rules.krk_opposition_check
#check @EndgameChess.Rules.krk_opposition_four_ply
#check @EndgameChess.Rules.krk_opposition_edge_force

-- S028: proved image bounds, bounded rank contraction/rescue and fixed controls.
#print axioms EndgameChess.Rules.phase_image_of_replies
#print axioms EndgameChess.Rules.krk_follow_check_image
#print axioms EndgameChess.Rules.krk_opposition_phase_image
#print axioms EndgameChess.Rules.rank_advance_step
#print axioms EndgameChess.Rules.rank_advance_reply_exists
#print axioms EndgameChess.Rules.krk_rank_advance
#print axioms EndgameChess.Rules.barrier_horizontal_reply_exists
#print axioms EndgameChess.Rules.krk_barrier_rook_rescue
#print axioms EndgameChess.Rules.krk_rank_advance_rescue
#print axioms EndgameChess.Rules.phase_image_file_margin
#print axioms EndgameChess.Rules.krk_phase_image_upper_advance
#print axioms EndgameChess.Rules.phase_image_chase_cycle
#print axioms EndgameChess.Rules.protected_corner_reentry_stalemate
#print axioms EndgameChess.Rules.lower_band_raise_crossing
#print axioms EndgameChess.Rules.two_file_rank_raise_needs_rescue
#check @EndgameChess.Rules.phase_image_of_replies
#check @EndgameChess.Rules.krk_follow_check_image
#check @EndgameChess.Rules.krk_opposition_phase_image
#check @EndgameChess.Rules.rank_advance_step
#check @EndgameChess.Rules.rank_advance_reply_exists
#check @EndgameChess.Rules.krk_rank_advance
#check @EndgameChess.Rules.barrier_horizontal_reply_exists
#check @EndgameChess.Rules.krk_barrier_rook_rescue
#check @EndgameChess.Rules.krk_rank_advance_rescue
#check @EndgameChess.Rules.phase_image_file_margin
#check @EndgameChess.Rules.krk_phase_image_upper_advance
#check @EndgameChess.Rules.phase_image_chase_cycle
#check @EndgameChess.Rules.protected_corner_reentry_stalemate
#check @EndgameChess.Rules.lower_band_raise_crossing
#check @EndgameChess.Rules.two_file_rank_raise_needs_rescue
