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

-- S029: two-file check, bounded pursuit, closed rank-wall forcing and setup controls.
#print axioms EndgameChess.Rules.pursuitFile_bound
#print axioms EndgameChess.Rules.pursuit_absDiff
#print axioms EndgameChess.Rules.wall_far_margin
#print axioms EndgameChess.Rules.wall_wait_choice
#print axioms EndgameChess.Rules.krk_wall_rook_move
#print axioms EndgameChess.Rules.lower_band_reply_shape
#print axioms EndgameChess.Rules.pursuit_king_step
#print axioms EndgameChess.Rules.krk_pursuit_king_move
#print axioms EndgameChess.Rules.opposition_check_step_two
#print axioms EndgameChess.Rules.krk_opposition_check_two
#print axioms EndgameChess.Rules.krk_two_file_edge_force
#print axioms EndgameChess.Rules.pursuit_tempo_return_margin
#print axioms EndgameChess.Rules.pursuit_file_eq
#print axioms EndgameChess.Rules.pursuit_margin_step
#print axioms EndgameChess.Rules.krk_oriented_lower_pursuit
#print axioms EndgameChess.Rules.krk_lower_band_force_of_exits
#print axioms EndgameChess.Rules.krk_rank_wall_force
#print axioms EndgameChess.Rules.krk_phase_image_force
#print axioms EndgameChess.Rules.krk_vertical_wall_entry_force
#print axioms EndgameChess.Rules.two_file_edge_forcing_control
#print axioms EndgameChess.Rules.former_chase_cycle_is_forcing
#print axioms EndgameChess.Rules.threatened_wall_rook_is_forcing
#print axioms EndgameChess.Rules.direct_setup_capture_controls
#check @EndgameChess.Rules.pursuitFile_bound
#check @EndgameChess.Rules.pursuit_absDiff
#check @EndgameChess.Rules.wall_far_margin
#check @EndgameChess.Rules.wall_wait_choice
#check @EndgameChess.Rules.krk_wall_rook_move
#check @EndgameChess.Rules.lower_band_reply_shape
#check @EndgameChess.Rules.pursuit_king_step
#check @EndgameChess.Rules.krk_pursuit_king_move
#check @EndgameChess.Rules.opposition_check_step_two
#check @EndgameChess.Rules.krk_opposition_check_two
#check @EndgameChess.Rules.krk_two_file_edge_force
#check @EndgameChess.Rules.pursuit_tempo_return_margin
#check @EndgameChess.Rules.pursuit_file_eq
#check @EndgameChess.Rules.pursuit_margin_step
#check @EndgameChess.Rules.krk_oriented_lower_pursuit
#check @EndgameChess.Rules.krk_lower_band_force_of_exits
#check @EndgameChess.Rules.krk_rank_wall_force
#check @EndgameChess.Rules.krk_phase_image_force
#check @EndgameChess.Rules.krk_vertical_wall_entry_force
#check @EndgameChess.Rules.two_file_edge_forcing_control
#check @EndgameChess.Rules.former_chase_cycle_is_forcing
#check @EndgameChess.Rules.threatened_wall_rook_is_forcing
#check @EndgameChess.Rules.direct_setup_capture_controls

-- S030: safe setup, forcing transport and weak-turn classification.
#print axioms EndgameChess.Rules.krk_unprotected_capture
#print axioms EndgameChess.Rules.krk_force_weak_safe
#print axioms EndgameChess.Rules.noRights_after_legal
#print axioms EndgameChess.Rules.canCastle_noRights
#print axioms EndgameChess.Rules.krk_strong_reply
#print axioms EndgameChess.Rules.krk_force_transport
#print axioms EndgameChess.Rules.krk_axis_wall_force
#print axioms EndgameChess.Rules.krk_axis_entry_force
#print axioms EndgameChess.Rules.krk_setup_axis
#print axioms EndgameChess.Rules.krk_strong_arrival_geometry
#print axioms EndgameChess.Rules.krk_clear_vertical_entry_force
#print axioms EndgameChess.Rules.krk_clear_axis_entry_force
#print axioms EndgameChess.Rules.krk_horizontal_entry_force
#print axioms EndgameChess.Rules.krk_offrank_setup_force
#print axioms EndgameChess.Rules.krk_same_rank_retreat_force
#print axioms EndgameChess.Rules.krk_backrank_protected_force
#print axioms EndgameChess.Rules.krk_backrank_setup_force
#print axioms EndgameChess.Rules.krk_strong_force_of_not_check
#print axioms EndgameChess.Rules.krk_strong_arrival_force
#print axioms EndgameChess.Rules.krk_weak_force_iff
#print axioms EndgameChess.Rules.krk_weak_force_safe_iff
#print axioms EndgameChess.Rules.backrank_preparation_forces
#print axioms EndgameChess.Rules.black_flagged_file_setup_forces
#print axioms EndgameChess.Rules.safe_setup_capture_controls
#check @EndgameChess.Rules.krk_unprotected_capture
#check @EndgameChess.Rules.krk_force_weak_safe
#check @EndgameChess.Rules.noRights_after_legal
#check @EndgameChess.Rules.canCastle_noRights
#check @EndgameChess.Rules.krk_strong_reply
#check @EndgameChess.Rules.krk_force_transport
#check @EndgameChess.Rules.krk_axis_wall_force
#check @EndgameChess.Rules.krk_axis_entry_force
#check @EndgameChess.Rules.krk_setup_axis
#check @EndgameChess.Rules.krk_strong_arrival_geometry
#check @EndgameChess.Rules.krk_clear_vertical_entry_force
#check @EndgameChess.Rules.krk_clear_axis_entry_force
#check @EndgameChess.Rules.krk_horizontal_entry_force
#check @EndgameChess.Rules.krk_offrank_setup_force
#check @EndgameChess.Rules.krk_same_rank_retreat_force
#check @EndgameChess.Rules.krk_backrank_protected_force
#check @EndgameChess.Rules.krk_backrank_setup_force
#check @EndgameChess.Rules.krk_strong_force_of_not_check
#check @EndgameChess.Rules.krk_strong_arrival_force
#check @EndgameChess.Rules.krk_weak_force_iff
#check @EndgameChess.Rules.krk_weak_force_safe_iff
#check @EndgameChess.Rules.backrank_preparation_forces
#check @EndgameChess.Rules.black_flagged_file_setup_forces
#check @EndgameChess.Rules.safe_setup_capture_controls

-- S033 / EC-C022: exact abstract interface, recurrence and two projection results.
#print EndgameChess.Rules.HistoryLayer.Layer
#print EndgameChess.Rules.HistoryLayer.Goal
#print EndgameChess.Rules.HistoryLayer.RuleMateWithin
#print EndgameChess.Rules.HistoryLayer.RuleForceMate
#print axioms EndgameChess.Rules.HistoryLayer.ruleMateWithin_project
#print axioms EndgameChess.Rules.HistoryLayer.ruleForceMate_project
#check @EndgameChess.Rules.HistoryLayer.ruleMateWithin_project
#check @EndgameChess.Rules.HistoryLayer.ruleForceMate_project

-- S035 / EC-C023: concrete raw trace data and full append lifting.
#print EndgameChess.Rules.RawTrace.Trace
#print EndgameChess.Rules.RawTrace.Trace.moves
#print EndgameChess.Rules.RawTrace.Trace.positions
#print EndgameChess.Rules.RawTrace.State
#print EndgameChess.Rules.RawTrace.erase
#print EndgameChess.Rules.RawTrace.initialState
#print EndgameChess.Rules.RawTrace.append
#print EndgameChess.Rules.RawTrace.RawBoardStep
#print axioms EndgameChess.Rules.RawTrace.append_spec
#print axioms EndgameChess.Rules.RawTrace.raw_step_sound
#print axioms EndgameChess.Rules.RawTrace.raw_step_complete
#print axioms EndgameChess.Rules.RawTrace.trace_arisen
#check @EndgameChess.Rules.RawTrace.append_spec
#check @EndgameChess.Rules.RawTrace.raw_step_sound
#check @EndgameChess.Rules.RawTrace.raw_step_complete
#check @EndgameChess.Rules.RawTrace.trace_arisen

-- S036 / EC-C024: raw halfmove fold, event semantics and ply bounds.
#print EndgameChess.Rules.RawClock.Pawn
#print EndgameChess.Rules.RawClock.zeroing
#print EndgameChess.Rules.RawClock.CaptureEvent
#print EndgameChess.Rules.RawClock.clock
#check @EndgameChess.Rules.RawClock.event_cases
#print axioms EndgameChess.Rules.RawClock.event_cases
#check @EndgameChess.Rules.RawClock.legal_zero_iff
#print axioms EndgameChess.Rules.RawClock.legal_zero_iff
#check @EndgameChess.Rules.RawClock.castle_empty
#print axioms EndgameChess.Rules.RawClock.castle_empty
#check @EndgameChess.Rules.RawClock.append_clock
#print axioms EndgameChess.Rules.RawClock.append_clock
#check @EndgameChess.Rules.RawClock.clock_le_length
#print axioms EndgameChess.Rules.RawClock.clock_le_length
#check @EndgameChess.Rules.RawClock.append_clock_le
#print axioms EndgameChess.Rules.RawClock.append_clock_le

-- S038 / EC-C025: actual finite extensions and raw multi-step bound.
#print EndgameChess.Rules.RawTrace.Extends
#check @EndgameChess.Rules.RawClock.clock_le_extension
#print axioms EndgameChess.Rules.RawClock.clock_le_extension

-- S040 / EC-C026: explicit-hypothesis prefix and prospective-ply clock certificate.
#check @EndgameChess.Rules.RawClock.clock_budget_certificate
#print axioms EndgameChess.Rules.RawClock.clock_budget_certificate
