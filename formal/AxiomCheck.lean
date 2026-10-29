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

-- S042 / EC-C027: generic full-history key count and exact append law.
#print EndgameChess.Rules.RawOccurrences.occurrences
#check @EndgameChess.Rules.RawOccurrences.append_occurrences
#print axioms EndgameChess.Rules.RawOccurrences.append_occurrences

-- S044 / EC-C028: actual legal ep event and effective target consistency.
#print EndgameChess.Rules.RawRepetition.LegalEP
#print EndgameChess.Rules.RawRepetition.effectiveEP
#check @EndgameChess.Rules.RawRepetition.effectiveEP_spec
#print axioms EndgameChess.Rules.RawRepetition.effectiveEP_spec

-- S046 / EC-C029: recover the full ep event from actual legal empty-dst pawn shape.
#check @EndgameChess.Rules.RawRepetition.legalEP_iff_shape
#print axioms EndgameChess.Rules.RawRepetition.legalEP_iff_shape
#print axioms EndgameChess.Rules.RawRepetition.ordinary_ep_irrelevance
#check @EndgameChess.Rules.RawRepetition.ordinary_ep_irrelevance
#print axioms EndgameChess.Rules.RawRepetition.normalizeEP_preserves
#check @EndgameChess.Rules.RawRepetition.normalizeEP_preserves
#print axioms EndgameChess.Rules.RawRepetition.key_legal_congr
#check @EndgameChess.Rules.RawRepetition.key_legal_congr
#print axioms EndgameChess.Rules.RawRepetition.append_currentOccurrences
#check @EndgameChess.Rules.RawRepetition.append_currentOccurrences
#print axioms EndgameChess.Rules.RawClaims.no_threshold_certificate
#check @EndgameChess.Rules.RawClaims.no_threshold_certificate
#print axioms EndgameChess.Rules.RawClaims.no_threshold_iff
#check @EndgameChess.Rules.RawClaims.no_threshold_iff
#print axioms EndgameChess.Rules.RawAdjudication.ongoing_iff
#check @EndgameChess.Rules.RawAdjudication.ongoing_iff
#print axioms EndgameChess.Rules.StoppedHistory.append_and_reply_lifting
#check @EndgameChess.Rules.StoppedHistory.append_and_reply_lifting
#print axioms EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_project
#check @EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_project
#print axioms EndgameChess.Rules.RawTrace.extends_prepend
#check @EndgameChess.Rules.RawTrace.extends_prepend
#print axioms EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_of_budget
#check @EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_of_budget

/-! EC-C040: explicit 508-ply KRK strategy and all public helpers. -/
#print axioms EndgameChess.Rules.krk_strong_arrival_bound
#check @EndgameChess.Rules.krk_strong_arrival_bound
#print axioms EndgameChess.Rules.krk_axis_entry_bound
#check @EndgameChess.Rules.krk_axis_entry_bound
#print axioms EndgameChess.Rules.krk_axis_wall_bound
#check @EndgameChess.Rules.krk_axis_wall_bound
#print axioms EndgameChess.Rules.krk_backrank_setup_bound
#check @EndgameChess.Rules.krk_backrank_setup_bound
#print axioms EndgameChess.Rules.mateWithin_choose
#check @EndgameChess.Rules.mateWithin_choose
#print axioms EndgameChess.Rules.krk_clear_axis_entry_bound
#check @EndgameChess.Rules.krk_clear_axis_entry_bound
#print axioms EndgameChess.Rules.krk_clear_vertical_entry_bound
#check @EndgameChess.Rules.krk_clear_vertical_entry_bound
#print axioms EndgameChess.Rules.mateWithin_defend
#check @EndgameChess.Rules.mateWithin_defend
#print axioms EndgameChess.Rules.krk_vertical_wall_entry_bound
#check @EndgameChess.Rules.krk_vertical_wall_entry_bound
#print axioms EndgameChess.Rules.krk_horizontal_entry_bound
#check @EndgameChess.Rules.krk_horizontal_entry_bound
#print axioms EndgameChess.Rules.krk_lower_band_bound_of_exits
#check @EndgameChess.Rules.krk_lower_band_bound_of_exits
#print axioms EndgameChess.Rules.krk_strong_bound_of_not_check
#check @EndgameChess.Rules.krk_strong_bound_of_not_check
#print axioms EndgameChess.Rules.krk_offrank_setup_bound
#check @EndgameChess.Rules.krk_offrank_setup_bound
#print axioms EndgameChess.Rules.mateWithin_pair
#check @EndgameChess.Rules.mateWithin_pair
#print axioms EndgameChess.Rules.positive_setup_bound
#check @EndgameChess.Rules.positive_setup_bound
#print axioms EndgameChess.Rules.krk_backrank_protected_bound
#check @EndgameChess.Rules.krk_backrank_protected_bound
#print axioms EndgameChess.Rules.krk_oriented_lower_bound
#check @EndgameChess.Rules.krk_oriented_lower_bound
#print axioms EndgameChess.Rules.bound_rank_zero_reply
#check @EndgameChess.Rules.bound_rank_zero_reply
#print axioms EndgameChess.Rules.krk_same_rank_retreat_bound
#check @EndgameChess.Rules.krk_same_rank_retreat_bound
#print axioms EndgameChess.Rules.bound_same_rank_no_file
#check @EndgameChess.Rules.bound_same_rank_no_file
#print axioms EndgameChess.Rules.krk_bound_transport
#check @EndgameChess.Rules.krk_bound_transport
#print axioms EndgameChess.Rules.krk_rank_wall_bound
#check @EndgameChess.Rules.krk_rank_wall_bound
#print axioms EndgameChess.Rules.krk_wall_ceiling
#check @EndgameChess.Rules.krk_wall_ceiling
#print axioms EndgameChess.Rules.bound_weak_wall
#check @EndgameChess.Rules.bound_weak_wall

/-! EC-C041: key-simple all-defence KRK rank strategy. -/
#print axioms EndgameChess.Rules.krk_key_simple_strategy
#check @EndgameChess.Rules.krk_key_simple_strategy
#print axioms EndgameChess.Rules.strategy_key_budget
#check @EndgameChess.Rules.strategy_key_budget
#print axioms EndgameChess.Rules.strategy_key_interface
#check @EndgameChess.Rules.strategy_key_interface
#print axioms EndgameChess.Rules.strategy_least_budget
#check @EndgameChess.Rules.strategy_least_budget
#print axioms EndgameChess.Rules.strategy_line_certificate
#check @EndgameChess.Rules.strategy_line_certificate
#print axioms EndgameChess.Rules.strategy_progress
#check @EndgameChess.Rules.strategy_progress
#print axioms EndgameChess.Rules.strategy_rank_key
#check @EndgameChess.Rules.strategy_rank_key
#print axioms EndgameChess.Rules.strategy_rank_spec
#check @EndgameChess.Rules.strategy_rank_spec
#print axioms EndgameChess.Rules.strategy_terminal
#check @EndgameChess.Rules.strategy_terminal

/-! EC-C042: actual-history rank-policy lifting and 84-ply RAW wall family. -/
#print axioms EndgameChess.Rules.RawHistoryLayer.strategy_append_history
#check @EndgameChess.Rules.RawHistoryLayer.strategy_append_history
#print axioms EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_of_strategy_history
#check @EndgameChess.Rules.RawHistoryLayer.raw_ruleMateWithin_of_strategy_history
#print axioms EndgameChess.Rules.RawHistoryLayer.raw_rank_six_wall_ruleMateWithin
#check @EndgameChess.Rules.RawHistoryLayer.raw_rank_six_wall_ruleMateWithin

/-! EC-C043: file/rank edge savings, credited walls and RAW clock coverage. -/
#print axioms EndgameChess.Rules.krk_axis_wall_bound_sharper
#check @EndgameChess.Rules.krk_axis_wall_bound_sharper
#print axioms EndgameChess.Rules.krk_lower_band_bound_of_exits_sharper
#check @EndgameChess.Rules.krk_lower_band_bound_of_exits_sharper
#print axioms EndgameChess.Rules.krk_oriented_lower_bound_sharper
#check @EndgameChess.Rules.krk_oriented_lower_bound_sharper
#print axioms EndgameChess.Rules.RawHistoryLayer.raw_axis_rank_six_wall_ruleMateWithin_sharper
#check @EndgameChess.Rules.RawHistoryLayer.raw_axis_rank_six_wall_ruleMateWithin_sharper
#print axioms EndgameChess.Rules.krk_rank_wall_bound_sharper
#check @EndgameChess.Rules.krk_rank_wall_bound_sharper

/-! EC-C044: actual parametric KRK setup and global442/443 bounds. -/
#print axioms EndgameChess.Rules.setup_arrival_budget
#check @EndgameChess.Rules.setup_arrival_budget
#print axioms EndgameChess.Rules.setup_axis_wall_budget
#check @EndgameChess.Rules.setup_axis_wall_budget
#print axioms EndgameChess.Rules.setup_backrank_budget
#check @EndgameChess.Rules.setup_backrank_budget
#print axioms EndgameChess.Rules.setup_clear_axis_entry_budget
#check @EndgameChess.Rules.setup_clear_axis_entry_budget
#print axioms EndgameChess.Rules.setup_clear_entry_budget
#check @EndgameChess.Rules.setup_clear_entry_budget
#print axioms EndgameChess.Rules.setup_horizontal_entry_budget
#check @EndgameChess.Rules.setup_horizontal_entry_budget
#print axioms EndgameChess.Rules.setup_strong_budget_of_not_check
#check @EndgameChess.Rules.setup_strong_budget_of_not_check
#print axioms EndgameChess.Rules.setup_offrank_budget
#check @EndgameChess.Rules.setup_offrank_budget
#print axioms EndgameChess.Rules.setup_positive_budget
#check @EndgameChess.Rules.setup_positive_budget
#print axioms EndgameChess.Rules.setup_protected_entry_budget
#check @EndgameChess.Rules.setup_protected_entry_budget
#print axioms EndgameChess.Rules.setup_same_rank_budget
#check @EndgameChess.Rules.setup_same_rank_budget
#print axioms EndgameChess.Rules.krk_strong_arrival_bound_442
#check @EndgameChess.Rules.krk_strong_arrival_bound_442
#print axioms EndgameChess.Rules.krk_weak_forcing_bound_443
#check @EndgameChess.Rules.krk_weak_forcing_bound_443
#print axioms EndgameChess.Rules.krk_wall_uniform_438
#check @EndgameChess.Rules.krk_wall_uniform_438
#print axioms EndgameChess.Rules.setup_weak_safe_budget
#check @EndgameChess.Rules.setup_weak_safe_budget
#print axioms EndgameChess.Rules.setup_weak_wall_budget
#check @EndgameChess.Rules.setup_weak_wall_budget

/-! EC-C045: universal admitted RAW KRK clock-bounded termination. -/
#print axioms EndgameChess.Rules.krk_material_targets
#check @EndgameChess.Rules.krk_material_targets
#print axioms EndgameChess.Rules.krk_castle_material
#check @EndgameChess.Rules.krk_castle_material
#print axioms EndgameChess.Rules.krk_strong_material
#check @EndgameChess.Rules.krk_strong_material
#print axioms EndgameChess.Rules.krk_legal_material_clock
#check @EndgameChess.Rules.krk_legal_material_clock
#print axioms EndgameChess.Rules.KRKTermination.step_parent_ongoing
#check @EndgameChess.Rules.KRKTermination.step_parent_ongoing
#print axioms EndgameChess.Rules.KRKTermination.step_decreases
#check @EndgameChess.Rules.KRKTermination.step_decreases
#print axioms EndgameChess.Rules.KRKTermination.path_bound
#check @EndgameChess.Rules.KRKTermination.path_bound
#print axioms EndgameChess.Rules.KRKTermination.krk_clock_cap
#check @EndgameChess.Rules.KRKTermination.krk_clock_cap
#print axioms EndgameChess.Rules.KRKTermination.maximal_iff_terminal
#check @EndgameChess.Rules.KRKTermination.maximal_iff_terminal
#print axioms EndgameChess.Rules.KRKTermination.terminal_continuation
#check @EndgameChess.Rules.KRKTermination.terminal_continuation

/-! EC-C046: actual all-history RAW KRK holding policies. -/
#print axioms EndgameChess.Rules.KRKHolding.budget_monotone
#check @EndgameChess.Rules.KRKHolding.budget_monotone
#print axioms EndgameChess.Rules.KRKHolding.fuel_saturation
#check @EndgameChess.Rules.KRKHolding.fuel_saturation
#print axioms EndgameChess.Rules.KRKHolding.defensive_choice
#check @EndgameChess.Rules.KRKHolding.defensive_choice
#print axioms EndgameChess.Rules.KRKHolding.holding_policy
#check @EndgameChess.Rules.KRKHolding.holding_policy
#print axioms EndgameChess.Rules.KRKHolding.hold_of_not_force
#check @EndgameChess.Rules.KRKHolding.hold_of_not_force
#print axioms EndgameChess.Rules.KRKHolding.not_force_of_hold
#check @EndgameChess.Rules.KRKHolding.not_force_of_hold
#print axioms EndgameChess.Rules.KRKHolding.holding_iff_not_force
#check @EndgameChess.Rules.KRKHolding.holding_iff_not_force
#print axioms EndgameChess.Rules.KRKHolding.policy_path_bound
#check @EndgameChess.Rules.KRKHolding.policy_path_bound
#print axioms EndgameChess.Rules.KRKHolding.policy_maximal_iff_stopped
#check @EndgameChess.Rules.KRKHolding.policy_maximal_iff_stopped
#print axioms EndgameChess.Rules.KRKHolding.stopped_continuation
#check @EndgameChess.Rules.KRKHolding.stopped_continuation

/-! EC-C047: universal strong nonloss and exact high-clock RAW KRK criteria. -/
#print axioms EndgameChess.Rules.KRKHighClock.arisen_no_weak_goal
#check @EndgameChess.Rules.KRKHighClock.arisen_no_weak_goal
#print axioms EndgameChess.Rules.KRKHighClock.good_step
#check @EndgameChess.Rules.KRKHighClock.good_step
#print axioms EndgameChess.Rules.KRKHighClock.good_no_weak_goal
#check @EndgameChess.Rules.KRKHighClock.good_no_weak_goal
#print axioms EndgameChess.Rules.KRKHighClock.strong_hold
#check @EndgameChess.Rules.KRKHighClock.strong_hold
#print axioms EndgameChess.Rules.KRKHighClock.weak_not_force
#check @EndgameChess.Rules.KRKHighClock.weak_not_force
#print axioms EndgameChess.Rules.KRKHighClock.terminal_force_iff_goal
#check @EndgameChess.Rules.KRKHighClock.terminal_force_iff_goal
#print axioms EndgameChess.Rules.KRKHighClock.winning_child_quiet
#check @EndgameChess.Rules.KRKHighClock.winning_child_quiet
#print axioms EndgameChess.Rules.KRKHighClock.weak_high_clock_not_force
#check @EndgameChess.Rules.KRKHighClock.weak_high_clock_not_force
#print axioms EndgameChess.Rules.KRKHighClock.strong_high_clock_iff
#check @EndgameChess.Rules.KRKHighClock.strong_high_clock_iff
#print axioms EndgameChess.Rules.KRKHighClock.high_clock_exact_one
#check @EndgameChess.Rules.KRKHighClock.high_clock_exact_one

/-! EC-C048: independent actual bounded winning policies and exact certificate bridge. -/
#print axioms EndgameChess.Rules.KRKWinning.forcing_actions
#check @EndgameChess.Rules.KRKWinning.forcing_actions
#print axioms EndgameChess.Rules.KRKWinning.winning_policy
#check @EndgameChess.Rules.KRKWinning.winning_policy
#print axioms EndgameChess.Rules.KRKWinning.winning_safety
#check @EndgameChess.Rules.KRKWinning.winning_safety
#print axioms EndgameChess.Rules.KRKWinning.actual_win_of_force
#check @EndgameChess.Rules.KRKWinning.actual_win_of_force
#print axioms EndgameChess.Rules.KRKWinning.policy_certificate
#check @EndgameChess.Rules.KRKWinning.policy_certificate
#print axioms EndgameChess.Rules.KRKWinning.actual_win_iff_force
#check @EndgameChess.Rules.KRKWinning.actual_win_iff_force
#print axioms EndgameChess.Rules.KRKWinning.winning_maximal_goal
#check @EndgameChess.Rules.KRKWinning.winning_maximal_goal
#print axioms EndgameChess.Rules.KRKWinning.winning_mate_continuation
#check @EndgameChess.Rules.KRKWinning.winning_mate_continuation

/-! EC-C049: actual clock-zero KRK history control and fresh73 wall coverage. -/
#print axioms EndgameChess.Rules.KRKFresh.key_material
#check @EndgameChess.Rules.KRKFresh.key_material
#print axioms EndgameChess.Rules.KRKFresh.prefix_region
#check @EndgameChess.Rules.KRKFresh.prefix_region
#print axioms EndgameChess.Rules.KRKFresh.clock_zero_counts
#check @EndgameChess.Rules.KRKFresh.clock_zero_counts
#print axioms EndgameChess.Rules.KRKFresh.winning_move_material
#check @EndgameChess.Rules.KRKFresh.winning_move_material
#print axioms EndgameChess.Rules.KRKFresh.restricted_append
#check @EndgameChess.Rules.KRKFresh.restricted_append
#print axioms EndgameChess.Rules.KRKFresh.restricted_lifting
#check @EndgameChess.Rules.KRKFresh.restricted_lifting
#print axioms EndgameChess.Rules.KRKFresh.clock_zero_sub100
#check @EndgameChess.Rules.KRKFresh.clock_zero_sub100
#print axioms EndgameChess.Rules.KRKFresh.clock_zero_axis_wall
#check @EndgameChess.Rules.KRKFresh.clock_zero_axis_wall

/-! EC-C051: guarded large-box phase; small-box finish remains open. -/
#print axioms EndgameChess.Rules.krk_box_reply_exists
#check @EndgameChess.Rules.krk_box_reply_exists
#print axioms EndgameChess.Rules.krk_box_reply_region
#check @EndgameChess.Rules.krk_box_reply_region
#print axioms EndgameChess.Rules.krk_guarded_large_box_phase
#check @EndgameChess.Rules.krk_guarded_large_box_phase
#print axioms EndgameChess.Rules.krk_guarded_large_box_cost
#check @EndgameChess.Rules.krk_guarded_large_box_cost
#print axioms EndgameChess.Rules.krk_width_four_escort_cycle
#check @EndgameChess.Rules.krk_width_four_escort_cycle

/-! EC-C052: integrated wall93, arrivals97/98 and complete RAW clock0 winning criterion. -/
#print axioms EndgameChess.Rules.KRKCentral.arrival97
#check @EndgameChess.Rules.KRKCentral.arrival97
#print axioms EndgameChess.Rules.KRKCentral.back_bound
#check @EndgameChess.Rules.KRKCentral.back_bound
#print axioms EndgameChess.Rules.KRKCentral.back_even_bound
#check @EndgameChess.Rules.KRKCentral.back_even_bound
#print axioms EndgameChess.Rules.KRKCentral.central_bound
#check @EndgameChess.Rules.KRKCentral.central_bound
#print axioms EndgameChess.Rules.KRKCentral.column_bound
#check @EndgameChess.Rules.KRKCentral.column_bound
#print axioms EndgameChess.Rules.KRKCentral.column_wall_bound
#check @EndgameChess.Rules.KRKCentral.column_wall_bound
#print axioms EndgameChess.Rules.KRKCentral.exit_step_bound
#check @EndgameChess.Rules.KRKCentral.exit_step_bound
#print axioms EndgameChess.Rules.KRKCentral.fresh_arrival97
#check @EndgameChess.Rules.KRKCentral.fresh_arrival97
#print axioms EndgameChess.Rules.KRKCentral.fresh_outcome
#check @EndgameChess.Rules.KRKCentral.fresh_outcome
#print axioms EndgameChess.Rules.KRKCentral.fresh_weak98
#check @EndgameChess.Rules.KRKCentral.fresh_weak98
#print axioms EndgameChess.Rules.KRKCentral.full_bound
#check @EndgameChess.Rules.KRKCentral.full_bound
#print axioms EndgameChess.Rules.KRKCentral.full_cut_bound
#check @EndgameChess.Rules.KRKCentral.full_cut_bound
#print axioms EndgameChess.Rules.KRKCentral.guarded_bound
#check @EndgameChess.Rules.KRKCentral.guarded_bound
#print axioms EndgameChess.Rules.KRKCentral.king_below_pair
#check @EndgameChess.Rules.KRKCentral.king_below_pair
#print axioms EndgameChess.Rules.KRKCentral.pivot_bound
#check @EndgameChess.Rules.KRKCentral.pivot_bound
#print axioms EndgameChess.Rules.KRKCentral.positive_bound
#check @EndgameChess.Rules.KRKCentral.positive_bound
#print axioms EndgameChess.Rules.KRKCentral.prep_bound
#check @EndgameChess.Rules.KRKCentral.prep_bound
#print axioms EndgameChess.Rules.KRKCentral.prep_pair
#check @EndgameChess.Rules.KRKCentral.prep_pair
#print axioms EndgameChess.Rules.KRKCentral.rank_two_pair
#check @EndgameChess.Rules.KRKCentral.rank_two_pair
#print axioms EndgameChess.Rules.KRKCentral.ready_bound
#check @EndgameChess.Rules.KRKCentral.ready_bound
#print axioms EndgameChess.Rules.KRKCentral.ready_cut_bound
#check @EndgameChess.Rules.KRKCentral.ready_cut_bound
#print axioms EndgameChess.Rules.KRKCentral.restoration_bound
#check @EndgameChess.Rules.KRKCentral.restoration_bound
#print axioms EndgameChess.Rules.KRKCentral.small_central_bound
#check @EndgameChess.Rules.KRKCentral.small_central_bound
#print axioms EndgameChess.Rules.KRKCentral.wait_even_bound
#check @EndgameChess.Rules.KRKCentral.wait_even_bound
#print axioms EndgameChess.Rules.KRKCentral.wall93
#check @EndgameChess.Rules.KRKCentral.wall93
#print axioms EndgameChess.Rules.KRKCentral.weak98
#check @EndgameChess.Rules.KRKCentral.weak98

/-! S092 working dependency: exact necessary optional-claim deadline. -/
#print axioms EndgameChess.Rules.KRKDeadline.winning_deadline
#check @EndgameChess.Rules.KRKDeadline.winning_deadline

/-! Working terminal geometry for the positive-clock lower-bound problem. -/
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_edge
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_necessity
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_sufficiency
#print axioms EndgameChess.Rules.KRKMateGeometry.mate_iff_terminal
#print axioms EndgameChess.Rules.KRKMateGeometry.king_step_not_mate
#print axioms EndgameChess.Rules.KRKMateGeometry.kernel_mate_model
#print axioms EndgameChess.Rules.KRKMateGeometry.kernel_mate_iff
#check @EndgameChess.Rules.KRKMateGeometry.kernel_mate_iff
#check @EndgameChess.Rules.KRKMateGeometry.king_step_not_mate

#print axioms EndgameChess.Rules.KRKMatingMove.castle_not_mate
#print axioms EndgameChess.Rules.KRKMatingMove.king_move_not_mate
#print axioms EndgameChess.Rules.KRKMatingMove.mating_source
#print axioms EndgameChess.Rules.KRKMatingMove.rook_move_model
#print axioms EndgameChess.Rules.KRKImmediate.immediate_iff
#print axioms EndgameChess.Rules.KRKImmediate.admitted_immediate_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKEdgeDepth.depth_step
#print axioms EndgameChess.Rules.KRKEdgeDepth.terminal_depth_zero
#print axioms EndgameChess.Rules.KRKEdgeDepth.ready_predecessor_depth_zero
#print axioms EndgameChess.Rules.KRKEdgeDepth.weak_interior_not_three
#print axioms EndgameChess.Rules.KRKEdgeDepth.arrival_far
#print axioms EndgameChess.Rules.KRKEdgeDepth.mate_depth_lower
#print axioms EndgameChess.Rules.KRKEdgeDepth.clock_depth_necessary
#print axioms EndgameChess.Rules.KRKEdgeDepth.clock_depth_holding
#check @EndgameChess.Rules.KRKImmediate.high_clock_actual_iff
#check @EndgameChess.Rules.KRKEdgeDepth.clock_depth_holding

#print axioms EndgameChess.Rules.KRKEdgeDepth.horizontal_predecessor
#print axioms EndgameChess.Rules.KRKLastReply.ready_neighbour_unique
#print axioms EndgameChess.Rules.KRKLastReply.model_last_iff
#print axioms EndgameChess.Rules.KRKLastReply.weak_two_iff
#print axioms EndgameChess.Rules.KRKLastReply.weak_three_iff
#print axioms EndgameChess.Rules.KRKLastReply.rule_two_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_exact_two
#print axioms EndgameChess.Rules.KRKLastReply.strong_two_to_one
#print axioms EndgameChess.Rules.KRKLastReply.unique_legal_reply
#print axioms EndgameChess.Rules.KRKLastReply.no_claim_at_unique_reply
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_actual_key_iff
#print axioms EndgameChess.Rules.KRKThreePly.castle_not_last
#print axioms EndgameChess.Rules.KRKThreePly.king_move_model
#print axioms EndgameChess.Rules.KRKThreePly.last_entry_move
#print axioms EndgameChess.Rules.KRKThreePly.strong_three_iff
#print axioms EndgameChess.Rules.KRKThreePly.entry_no_claim_iff
#print axioms EndgameChess.Rules.KRKThreePly.history_three_sufficient
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKFourPlyEscape.last_depth_zero
#print axioms EndgameChess.Rules.KRKFourPlyEscape.three_depth_zero
#print axioms EndgameChess.Rules.KRKFourPlyEscape.interior_neighbour_covered
#print axioms EndgameChess.Rules.KRKFourPlyEscape.covered_box
#print axioms EndgameChess.Rules.KRKFourPlyEscape.strip_prison
#print axioms EndgameChess.Rules.KRKFourPlyEscape.corner_prison
#print axioms EndgameChess.Rules.KRKFourPlyEscape.corner_escape
#print axioms EndgameChess.Rules.KRKFourPlyEscape.strip_escape
#print axioms EndgameChess.Rules.KRKFourPlyEscape.deep_prison_impossible
#print axioms EndgameChess.Rules.KRKFourPlyEscape.interior_four_impossible
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_four
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_five
#print axioms EndgameChess.Rules.KRKFourPlyEscape.mate_depth_lower
#print axioms EndgameChess.Rules.KRKFourPlyEscape.clock_depth_necessary
#print axioms EndgameChess.Rules.KRKFourPlyEscape.clock_depth_holding
#print axioms EndgameChess.Rules.KRKThreePly.last_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_middle_iff
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.central_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.opposition_replies
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.weak_four_iff
#print axioms EndgameChess.Rules.KRKLastReply.weak_move_eq
#print axioms EndgameChess.Rules.KRKLastReply.lone_step_legal
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_legal
#print axioms EndgameChess.Rules.KRKRookRayBarriers.ray_last_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.ray_sees_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKLastReply.weak_safe_quiet
#print axioms EndgameChess.Rules.KRKRookRayBarriers.return_legal
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_five_to_four
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_material_after
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_keys_ne
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_append_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_step_cases
#print axioms EndgameChess.Rules.KRKOppositionHistory.west_legal
#print axioms EndgameChess.Rules.KRKOppositionHistory.east_legal
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_force_no_claim
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_necessary
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_sufficient
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_exact_four
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKThreePly.last_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_near_iff

#print axioms EndgameChess.Rules.KRKThreePly.last_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_corner_iff
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.covered_or_middle
#print axioms EndgameChess.Rules.KRKFourPlySecond.covered_or_near
#print axioms EndgameChess.Rules.KRKFourPlySecond.second_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlySecond.opposition_replies
#print axioms EndgameChess.Rules.KRKFourPlySecond.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyEscape.three_map
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.covered_or_swapped_near
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_replies
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_safe
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_replies
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_safe
#print axioms EndgameChess.Rules.KRKFourPlyCorner.weak_four_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_legal
#print axioms EndgameChess.Rules.KRKThreePly.canonical_king_material
#print axioms EndgameChess.Rules.KRKNearKingBarrier.king_history_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.rook_history_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKOppositionHistory.append_query
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged_of_last
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_append_iff_of_last
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.king_queries_unchanged
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.king_append_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_ray_append_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_alternatives_append_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_force_data
#print axioms EndgameChess.Rules.KRKOppositionHistory.branch_necessary
#print axioms EndgameChess.Rules.KRKOppositionHistory.branch_certificate
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_necessary
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_certificate
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.second_necessary
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.second_sufficient
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_exact_four
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.flat_return_legal
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_sees_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKWeakPrefixEntry.entry_queries_unchanged
#print axioms EndgameChess.Rules.KRKWeakPrefixEntry.entry_append_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_far
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_not_rook
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_legal
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.ray_sees_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.line_target
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_swap_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_vertical_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.immediate_vertical_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.file_return_legal
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_sees_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSlotPrefix.Horizontal.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Horizontal.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Vertical.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Vertical.history_append_iff
#print axioms EndgameChess.Rules.KRKWeakBranch.history_geometry
#print axioms EndgameChess.Rules.KRKWeakBranch.child_clock
#print axioms EndgameChess.Rules.KRKWeakBranch.child_ongoing_of_force
#print axioms EndgameChess.Rules.KRKWeakBranch.child_history_of_force
#print axioms EndgameChess.Rules.KRKWeakBranch.child_certificate
#print axioms EndgameChess.Rules.KRKWeakBranch.admitted_far
#print axioms EndgameChess.Rules.KRKWeakBranch.weak_not_one
#print axioms EndgameChess.Rules.KRKCornerWeakBand.guard_legal
#print axioms EndgameChess.Rules.KRKCornerWeakBand.step_guard
#print axioms EndgameChess.Rules.KRKCornerWeakBand.neighbour_cases
#print axioms EndgameChess.Rules.KRKCornerWeakBand.necessary
#print axioms EndgameChess.Rules.KRKCornerWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_geometry
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_reply_distance
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.last_slots_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.flat_return_legal
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_sees_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.king_history_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.rook_history_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.immediate_second_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSlotPrefix.Second.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Second.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Corner.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Corner.history_append_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.neighbour_cases
#print axioms EndgameChess.Rules.KRKNearWeakBand.necessary
#print axioms EndgameChess.Rules.KRKNearWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_distance_cases

-- Global late-clock geometry with native history keys.
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_valid
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_valid
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_map
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_map_iff
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_map
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_map_iff
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.eq_iff
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.ne_iff
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.preimage_eq
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.map_step
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.map_inverse
#print axioms EndgameChess.Rules.KRKNativeFrame.bottomFrame_spec
#print axioms EndgameChess.Rules.KRKNativeFrame.normalize_spec
#print axioms EndgameChess.Rules.KRKCanonicalSlots.valid_bounds
#print axioms EndgameChess.Rules.KRKCanonicalSlots.last_catalogue_iff
#print axioms EndgameChess.Rules.KRKCanonicalSlots.slot_last
#print axioms EndgameChess.Rules.KRKCanonicalSlots.king_far
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_distance
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_far
#print axioms EndgameChess.Rules.KRKCanonicalSlots.region_off_reply
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_step
#print axioms EndgameChess.Rules.KRKCanonicalSlots.region_off_weak
#print axioms EndgameChess.Rules.KRKFramedHistory.ray_sees_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.native_reply_step
#print axioms EndgameChess.Rules.KRKFramedHistory.king_history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.rook_history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKFramedPrefix.point_append
#print axioms EndgameChess.Rules.KRKFramedPrefix.ray_append
#print axioms EndgameChess.Rules.KRKFramedPrefix.clear_append_iff
#print axioms EndgameChess.Rules.KRKFramedPrefix.history_append_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.necessary
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_distance_cases

-- Complete strong >=94 band and exact one/three/five distances.
#print axioms EndgameChess.Rules.KRKFourGeometry.three_map
#print axioms EndgameChess.Rules.KRKFourGeometry.three_iff
#print axioms EndgameChess.Rules.KRKFourGeometry.framed_shape_necessary
#print axioms EndgameChess.Rules.KRKFourGeometry.global_shape_necessary
#print axioms EndgameChess.Rules.KRKCastleFour.queen_geometry
#print axioms EndgameChess.Rules.KRKCastleFour.king_geometry
#print axioms EndgameChess.Rules.KRKCastleFour.king_square
#print axioms EndgameChess.Rules.KRKCastleFour.rook_square
#print axioms EndgameChess.Rules.KRKCastleFour.castle_not_four
#print axioms EndgameChess.Rules.KRKCastleFour.four_entry_move
#print axioms EndgameChess.Rules.KRKFourSlots.shape_iff
#print axioms EndgameChess.Rules.KRKFourSlots.entry_candidates
#print axioms EndgameChess.Rules.KRKFourSlots.high_clock_necessary
#print axioms EndgameChess.Rules.KRKStrongPrefix.strong_quiet
#print axioms EndgameChess.Rules.KRKStrongPrefix.occurrences_append
#print axioms EndgameChess.Rules.KRKStrongPrefix.original_entry_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.clear_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_clear_ongoing
#print axioms EndgameChess.Rules.KRKOrdinaryEntry.king_legal
#print axioms EndgameChess.Rules.KRKOrdinaryEntry.rook_legal
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_one_goal
#print axioms EndgameChess.Rules.KRKDistanceParity.strong_two_one
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_three_two
#print axioms EndgameChess.Rules.KRKDistanceParity.strong_four_three
#print axioms EndgameChess.Rules.KRKThreePlyExact.history_three_iff
#print axioms EndgameChess.Rules.KRKThreePlyExact.global_three_iff
#print axioms EndgameChess.Rules.KRKThreePlyExact.not_immediate_not_two
#print axioms EndgameChess.Rules.KRKFivePlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKFivePlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKFivePlyHistory.necessary
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_distance_cases

-- Complete weak >=93 band and exact two/four/six distances.
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.first_occurrences_eq
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.second_occurrences_eq
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.fourth_entry_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.inner_clear_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.weak_after_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.strong_clear_append_iff
#print axioms EndgameChess.Rules.KRKFourPlyExact.necessary
#print axioms EndgameChess.Rules.KRKFourPlyExact.rule_four_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.child_five_certificate
#print axioms EndgameChess.Rules.KRKSixPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKSixPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_clear_kernel
#print axioms EndgameChess.Rules.KRKFivePlyHistory.entry_kernel
#print axioms EndgameChess.Rules.KRKFivePlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_five_four

-- Deeper geometry and actual castling exclusion for strong >=92 entries.
#print axioms EndgameChess.Rules.KRKFiveGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKFiveGeometry.sufficient
#print axioms EndgameChess.Rules.KRKFiveGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKFiveGeometry.necessary
#print axioms EndgameChess.Rules.KRKFiveGeometry.kernel_five_iff
#print axioms EndgameChess.Rules.KRKSixGeometry.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixGeometry.strong_six_five
#print axioms EndgameChess.Rules.KRKSixGeometry.weak_seven_six
#print axioms EndgameChess.Rules.KRKCastleSix.five_depth_zero
#print axioms EndgameChess.Rules.KRKCastleSix.interior_covered
#print axioms EndgameChess.Rules.KRKCastleSix.rank_prison
#print axioms EndgameChess.Rules.KRKCastleSix.corner_prison
#print axioms EndgameChess.Rules.KRKCastleSix.cover_flip
#print axioms EndgameChess.Rules.KRKCastleSix.home_prison
#print axioms EndgameChess.Rules.KRKCastleSix.castle_not_six
#print axioms EndgameChess.Rules.KRKCastleSix.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKFourGeometry.framed_shape_sufficient
#print axioms EndgameChess.Rules.KRKFourGeometry.global_shape_sufficient

-- Compact five-ply middle formulas and six-ply destination restrictions.
#print axioms EndgameChess.Rules.KRKFiveMiddle.normalize_f
#print axioms EndgameChess.Rules.KRKFiveMiddle.normalize_r
#print axioms EndgameChess.Rules.KRKFiveMiddle.middle_slot_properties
#print axioms EndgameChess.Rules.KRKFiveMiddle.king_points_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.middle_reachable
#print axioms EndgameChess.Rules.KRKFiveMiddle.west_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.east_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.rook_rays_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.clear_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.kernel_five_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.bottom_clear_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.low_rook_bottom_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.rank_two_bottom_iff
#print axioms EndgameChess.Rules.KRKSixMiddle.covered_or_five
#print axioms EndgameChess.Rules.KRKSixMiddle.central_six_necessary
#print axioms EndgameChess.Rules.KRKSixMiddle.kernel_six_four_iff
#print axioms EndgameChess.Rules.KRKSixInterior.strip_escape
#print axioms EndgameChess.Rules.KRKSixInterior.interior_corner_necessary
#print axioms EndgameChess.Rules.KRKSixInterior.weak_six_interior_corner
#print axioms EndgameChess.Rules.KRKFiveGeometry.map
#print axioms EndgameChess.Rules.KRKFiveGeometry.map_iff

-- Complete interior six-ply geometry and strong >=92 interior drawing region.
#print axioms EndgameChess.Rules.KRKFiveNear.near_slot_properties
#print axioms EndgameChess.Rules.KRKFiveNear.king_points_iff
#print axioms EndgameChess.Rules.KRKFiveNear.west_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveNear.middle_reachable
#print axioms EndgameChess.Rules.KRKFiveNear.east_reachable
#print axioms EndgameChess.Rules.KRKFiveNear.rook_rays_iff
#print axioms EndgameChess.Rules.KRKFiveNear.clear_iff
#print axioms EndgameChess.Rules.KRKFiveNear.kernel_five_iff
#print axioms EndgameChess.Rules.KRKSixInwardCorner.near_from_step
#print axioms EndgameChess.Rules.KRKSixInwardCorner.horizontal_necessary
#print axioms EndgameChess.Rules.KRKSixInwardCorner.upper_escape
#print axioms EndgameChess.Rules.KRKSixInwardCorner.no_five_diagonal
#print axioms EndgameChess.Rules.KRKSixInwardCorner.necessary
#print axioms EndgameChess.Rules.KRKSixInwardCorner.horizontal_replies
#print axioms EndgameChess.Rules.KRKSixInwardCorner.replies_of_region
#print axioms EndgameChess.Rules.KRKSixInwardCorner.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixInwardCorner.region_clear
#print axioms EndgameChess.Rules.KRKSixInwardCorner.map_six
#print axioms EndgameChess.Rules.KRKSixInwardCorner.inner_sym_spec
#print axioms EndgameChess.Rules.KRKSixInwardCorner.global_kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixInwardCorner.global_kernel_exact_six
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.strong_eight_interior_corner
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_necessary
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_holding
#print axioms EndgameChess.Rules.KRKSixInterior.every_map

#print axioms EndgameChess.Rules.KRKSixCorner.blocked_or_near
#print axioms EndgameChess.Rules.KRKSixCorner.live_not_diagonal_rook
#print axioms EndgameChess.Rules.KRKSixCorner.corner_six_necessary
#print axioms EndgameChess.Rules.KRKSixCorner.region_swap
#print axioms EndgameChess.Rules.KRKSixCorner.region_excludes_inward
#print axioms EndgameChess.Rules.KRKSixCorner.region_south_five
#print axioms EndgameChess.Rules.KRKSixCorner.region_replies
#print axioms EndgameChess.Rules.KRKSixCorner.kernel_six_iff

#print axioms EndgameChess.Rules.KRKSixSecond.necessary
#print axioms EndgameChess.Rules.KRKSixSecond.region_replies
#print axioms EndgameChess.Rules.KRKSixSecond.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixSecond.new_geometry
#print axioms EndgameChess.Rules.KRKSixSecond.kernel_exact_six_iff

#print axioms EndgameChess.Rules.KRKFiveCornerEntries.slot22_properties
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_reachable
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_king_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.low_right_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.side_right_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.no_capture_square_entry
#print axioms EndgameChess.Rules.KRKSixNear.necessary
#print axioms EndgameChess.Rules.KRKSixNear.extra_replies
#print axioms EndgameChess.Rules.KRKSixNear.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixNear.kernel_exact_six_iff
#print axioms EndgameChess.Rules.KRKFrameBound.bound_transport
#print axioms EndgameChess.Rules.KRKFrameBound.five_map
#print axioms EndgameChess.Rules.KRKFrameBound.six_map
#print axioms EndgameChess.Rules.KRKSixGlobal.canonical_necessary
#print axioms EndgameChess.Rules.KRKSixGlobal.canonical_sufficient
#print axioms EndgameChess.Rules.KRKSixGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKSixGlobal.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixGlobal.kernel_exact_six_iff
#print axioms EndgameChess.Rules.KRKFivePlyExact.necessary
#print axioms EndgameChess.Rules.KRKFivePlyExact.rule_five_iff
#print axioms EndgameChess.Rules.KRKFivePlyExact.strong_six_five
#print axioms EndgameChess.Rules.KRKSevenPrefix.first_occurrences_root
#print axioms EndgameChess.Rules.KRKSevenPrefix.second_occurrences_root
#print axioms EndgameChess.Rules.KRKSevenPrefix.fourth_entry_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.inner_clear_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.weak_after_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.strong_clear_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.six_append_iff
#print axioms EndgameChess.Rules.KRKSevenSlots.region_bounds
#print axioms EndgameChess.Rules.KRKSevenSlots.region_point
#print axioms EndgameChess.Rules.KRKSevenEntry.six_entry_move
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.entry_kernel
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKSixPlyExact.necessary
#print axioms EndgameChess.Rules.KRKSixPlyExact.rule_six_iff
#print axioms EndgameChess.Rules.KRKSixPlyExact.weak_seven_six
#print axioms EndgameChess.Rules.KRKEightPrefix.prefix_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.root_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.first_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.second_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.fourth_entry_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.inner_clear_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.weak_after_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.strong_clear_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.six_after_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.seven_append_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.child_seven_certificate
#print axioms EndgameChess.Rules.KRKEightPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKEightPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSevenGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKSevenGeometry.sufficient
#print axioms EndgameChess.Rules.KRKSevenGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKSevenGeometry.necessary
#print axioms EndgameChess.Rules.KRKSevenGeometry.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKEightGeometry.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightGeometry.strong_eight_seven
#print axioms EndgameChess.Rules.KRKEightGeometry.weak_nine_eight
#print axioms EndgameChess.Rules.KRKSevenReach.region_weak_domain
#print axioms EndgameChess.Rules.KRKSevenReach.region_interior_distance
#print axioms EndgameChess.Rules.KRKSevenReach.weak_domain
#print axioms EndgameChess.Rules.KRKSevenReach.interior_king_near
#print axioms EndgameChess.Rules.KRKSevenReach.frame_map
#print axioms EndgameChess.Rules.KRKCastleEight.seven_bottom_interior
#print axioms EndgameChess.Rules.KRKCastleEight.above_covered
#print axioms EndgameChess.Rules.KRKCastleEight.rank_prison
#print axioms EndgameChess.Rules.KRKCastleEight.king_bottom_no_eight
#print axioms EndgameChess.Rules.KRKCastleEight.queen_bottom_weak_corner
#print axioms EndgameChess.Rules.KRKCastleEight.frame_map
#print axioms EndgameChess.Rules.KRKCastleEight.home_king_no_eight
#print axioms EndgameChess.Rules.KRKCastleEight.home_queen_weak_corner
#print axioms EndgameChess.Rules.KRKCastleEight.castle_not_eight
#print axioms EndgameChess.Rules.KRKCastleEight.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKSevenMiddle.kernel_seven_five_iff
#print axioms EndgameChess.Rules.KRKSevenMiddle.bottom_clear_iff
#print axioms EndgameChess.Rules.KRKSevenMiddle.low_rook_clear_iff
#print axioms EndgameChess.Rules.KRKSevenReach.king_step_clear
#print axioms EndgameChess.Rules.KRKSevenReach.rook_step_clear
#print axioms EndgameChess.Rules.KRKEightInterior.covered_or_inner
#print axioms EndgameChess.Rules.KRKEightInterior.deep_escape
#print axioms EndgameChess.Rules.KRKEightInterior.weak_eight_depth_le_one
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.strong_ten_depth_le_one
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.high_clock_depth_necessary
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.high_clock_deep_holding
#print axioms EndgameChess.Rules.KRKEightStrip.region_replies
#print axioms EndgameChess.Rules.KRKEightStrip.region_clear
#print axioms EndgameChess.Rules.KRKEightStrip.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKSevenNear.shape_iff
#print axioms EndgameChess.Rules.KRKSevenNear.reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenNear.rook_rays_iff
#print axioms EndgameChess.Rules.KRKSevenNear.clear_iff
#print axioms EndgameChess.Rules.KRKSevenNear.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKEightCentralStrip.prison
#print axioms EndgameChess.Rules.KRKEightCentralStrip.middle_not_clear
#print axioms EndgameChess.Rules.KRKEightCentralStrip.middle_kernel_no_eight
#print axioms EndgameChess.Rules.KRKEightCentralStripHolding.strong_no_ten
#print axioms EndgameChess.Rules.KRKEightCentralStripHolding.high_clock_holding
#print axioms EndgameChess.Rules.KRKEightNearStrip.prison
#print axioms EndgameChess.Rules.KRKSevenInner.inner_entry_necessary
#print axioms EndgameChess.Rules.KRKEightNearStrip.necessary
#print axioms EndgameChess.Rules.KRKEightNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKEightNearStrip.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightNearStrip.framed_clear_iff
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_line_necessary
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_line_sufficient
#print axioms EndgameChess.Rules.KRKSevenInner.necessary
#print axioms EndgameChess.Rules.KRKSevenInner.sufficient
#print axioms EndgameChess.Rules.KRKSevenInner.clear_iff
#print axioms EndgameChess.Rules.KRKSevenInner.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKEightInner.prison
#print axioms EndgameChess.Rules.KRKEightInner.row_two_necessary
#print axioms EndgameChess.Rules.KRKEightInner.file_one_necessary
#print axioms EndgameChess.Rules.KRKEightInner.no_seven_diagonal
#print axioms EndgameChess.Rules.KRKEightInner.diagonal_not_clear
#print axioms EndgameChess.Rules.KRKEightInner.necessary
#print axioms EndgameChess.Rules.KRKEightInner.horizontal_replies
#print axioms EndgameChess.Rules.KRKEightInner.horizontal_clear
#print axioms EndgameChess.Rules.KRKEightInner.sufficient
#print axioms EndgameChess.Rules.KRKEightInner.clear_iff
#print axioms EndgameChess.Rules.KRKEightInner.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightInner.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKEightInner.framed_clear_iff
#print axioms EndgameChess.Rules.KRKEightInteriorExact.strip_spec
#print axioms EndgameChess.Rules.KRKEightInteriorExact.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightInteriorExact.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKSevenSecond.shape_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.properties
#print axioms EndgameChess.Rules.KRKSevenSecond.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.rook_destination
#print axioms EndgameChess.Rules.KRKSevenSecond.rook_rays_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.clear_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKNineEntry.eight_entry_move
#print axioms EndgameChess.Rules.KRKNineNearStrip.rook_line_necessary
#print axioms EndgameChess.Rules.KRKNineNearStrip.rook_destination
#print axioms EndgameChess.Rules.KRKNineNearStrip.necessary
#print axioms EndgameChess.Rules.KRKNineNearStrip.sufficient
#print axioms EndgameChess.Rules.KRKNineNearStrip.kernel_nine_iff
#print axioms EndgameChess.Rules.KRKNineNearStrip.kernel_exact_nine
#print axioms EndgameChess.Rules.KRKSevenCorner.live_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.region_point
#print axioms EndgameChess.Rules.KRKSevenCorner.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_line_necessary
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_destination
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_rays_necessary
#print axioms EndgameChess.Rules.KRKSevenCorner.canonical_rook_clear
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_entries_sufficient
#print axioms EndgameChess.Rules.KRKSevenCorner.immediate_entries
#print axioms EndgameChess.Rules.KRKSevenCorner.clear_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKEightEdge.seven_test_iff
#print axioms EndgameChess.Rules.KRKEightEdge.reply_point
#print axioms EndgameChess.Rules.KRKEightEdge.clear_iff
#print axioms EndgameChess.Rules.KRKEightEdge.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.kernel_exact_eight_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.sufficient
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.necessary
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.exact_nine

#print axioms EndgameChess.Rules.KRKEightGlobal.region_live

#print axioms EndgameChess.Rules.KRKNineSlots.seven_test_rank

#print axioms EndgameChess.Rules.KRKNineSlots.edge_rank

#print axioms EndgameChess.Rules.KRKNineSlots.region_rank

#print axioms EndgameChess.Rules.KRKNineSlots.region_point

#print axioms EndgameChess.Rules.KRKNineGeometry.entry_sufficient

#print axioms EndgameChess.Rules.KRKNineGeometry.sufficient

#print axioms EndgameChess.Rules.KRKNineGeometry.entry_necessary

#print axioms EndgameChess.Rules.KRKNineGeometry.necessary

#print axioms EndgameChess.Rules.KRKNineGeometry.kernel_nine_iff

#print axioms EndgameChess.Rules.KRKNinePlyHistory.clear_geometry

#print axioms EndgameChess.Rules.KRKNinePlyHistory.clear_kernel

#print axioms EndgameChess.Rules.KRKNinePlyHistory.entry_certificate

#print axioms EndgameChess.Rules.KRKNinePlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKNinePlyHistory.necessary

#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKSevenPlyExact.necessary

#print axioms EndgameChess.Rules.KRKSevenPlyExact.rule_seven_iff

#print axioms EndgameChess.Rules.KRKSevenPlyExact.strong_eight_seven

#print axioms EndgameChess.Rules.KRKSevenPlyExact.weak_nine_eight

#print axioms EndgameChess.Rules.KRKSevenPlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKEightPlyExact.necessary

#print axioms EndgameChess.Rules.KRKEightPlyExact.rule_eight_iff

#print axioms EndgameChess.Rules.KRKEightPlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKNinePlyExact.necessary

#print axioms EndgameChess.Rules.KRKNinePlyExact.rule_nine_iff

#print axioms EndgameChess.Rules.KRKNinePlyExact.strong_ten_nine

#print axioms EndgameChess.Rules.KRKNinePlyExact.weak_eleven_ten

#print axioms EndgameChess.Rules.KRKNinePlyExact.high_clock_distance_split

#print axioms EndgameChess.Rules.KRKNinePlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKTenPlyHistory.after_weak_iff

#print axioms EndgameChess.Rules.KRKTenPlyHistory.child_nine_certificate

#print axioms EndgameChess.Rules.KRKTenPlyHistory.necessary

#print axioms EndgameChess.Rules.KRKTenPlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_hold_iff

#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKTenPlyExact.necessary

#print axioms EndgameChess.Rules.KRKTenPlyExact.rule_ten_iff

#print axioms EndgameChess.Rules.KRKTenPlyExact.high_clock_distance_split

#print axioms EndgameChess.Rules.KRKTenPlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKNineGeometry.frame_map

#print axioms EndgameChess.Rules.KRKTenGeometry.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenGeometry.strong_ten_nine

#print axioms EndgameChess.Rules.KRKTenGeometry.weak_eleven_ten

#print axioms EndgameChess.Rules.KRKTenGeometry.eight_region_depth

#print axioms EndgameChess.Rules.KRKTenGeometry.nine_weak_depth

#print axioms EndgameChess.Rules.KRKTenGeometry.frame_map

#print axioms EndgameChess.Rules.KRKTenSecondCorner.bad_neighbour_covered

#print axioms EndgameChess.Rules.KRKTenSecondCorner.prison

#print axioms EndgameChess.Rules.KRKTenSecondCorner.horizontal_escape

#print axioms EndgameChess.Rules.KRKTenSecondCorner.not_clear

#print axioms EndgameChess.Rules.KRKTenSecondCorner.framed_not_clear

#print axioms EndgameChess.Rules.KRKTenSecondCorner.kernel_no_ten

#print axioms EndgameChess.Rules.KRKTenSecondCorner.framed_kernel_no_ten

#print axioms EndgameChess.Rules.KRKTenSecondCornerHolding.strong_no_twelve

#print axioms EndgameChess.Rules.KRKTenSecondCornerHolding.high_clock_holding

#print axioms EndgameChess.Rules.KRKTenInterior.central_escape

#print axioms EndgameChess.Rules.KRKTenInterior.deep_not_clear

#print axioms EndgameChess.Rules.KRKTenInterior.weak_ten_depth_le_one

#print axioms EndgameChess.Rules.KRKTenInteriorHolding.strong_twelve_depth_le_one

#print axioms EndgameChess.Rules.KRKTenInteriorHolding.high_clock_depth_necessary

#print axioms EndgameChess.Rules.KRKTenInteriorHolding.high_clock_deep_holding

#print axioms EndgameChess.Rules.KRKNineNearStrip.clear_iff

#print axioms EndgameChess.Rules.KRKNineMiddleLow.eight_no_high_king

#print axioms EndgameChess.Rules.KRKNineMiddleLow.eight_low_necessary

#print axioms EndgameChess.Rules.KRKNineMiddleLow.no_nine

#print axioms EndgameChess.Rules.KRKTenCentralStrip.prison

#print axioms EndgameChess.Rules.KRKTenCentralStrip.row_four_no_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.upper_no_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.opposition_no_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.not_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.framed_not_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.file_one_not_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.middle_not_clear

#print axioms EndgameChess.Rules.KRKTenCentralStrip.middle_kernel_no_ten

#print axioms EndgameChess.Rules.KRKTenCentralStripHolding.strong_no_twelve

#print axioms EndgameChess.Rules.KRKTenCentralStripHolding.high_clock_holding

#print axioms EndgameChess.Rules.KRKNineGeometry.king_step_clear

#print axioms EndgameChess.Rules.KRKNineGeometry.rook_step_clear

#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_necessary

#print axioms EndgameChess.Rules.KRKNineMiddleLow.four_five_eight_clear

#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_sufficient

#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_iff

#print axioms EndgameChess.Rules.KRKNineInnerBoundary.inner_region

#print axioms EndgameChess.Rules.KRKNineInnerBoundary.rook_two_zero_high

#print axioms EndgameChess.Rules.KRKNineInnerBoundary.rook_two_three_right_high

#print axioms EndgameChess.Rules.KRKNineSecondBoundary.no_nine

#print axioms EndgameChess.Rules.KRKNineUpperEntries.near_entry

#print axioms EndgameChess.Rules.KRKNineUpperEntries.second_entry

#print axioms EndgameChess.Rules.KRKTenNearStrip.lower_neighbour_covered

#print axioms EndgameChess.Rules.KRKTenNearStrip.no_lower_guard

#print axioms EndgameChess.Rules.KRKTenNearStrip.prison

#print axioms EndgameChess.Rules.KRKTenNearStrip.row_three_clear

#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_row_three_exact_ten

#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_necessary

#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_clear

#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_iff

#print axioms EndgameChess.Rules.KRKTenNearStrip.upper_necessary

#print axioms EndgameChess.Rules.KRKTenNearStrip.necessary

#print axioms EndgameChess.Rules.KRKTenNearStrip.upper_clear

#print axioms EndgameChess.Rules.KRKTenNearStrip.sufficient

#print axioms EndgameChess.Rules.KRKTenNearStrip.clear_iff

#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_exact_ten

#print axioms EndgameChess.Rules.KRKTenNearStrip.framed_clear_iff

#print axioms EndgameChess.Rules.KRKTenNearStrip.diagonal_near_eight_clear

#print axioms EndgameChess.Rules.KRKNineInner.horizontal_shape

#print axioms EndgameChess.Rules.KRKNineInner.global_region_iff

#print axioms EndgameChess.Rules.KRKNineInner.king_points_iff

#print axioms EndgameChess.Rules.KRKNineInner.rook_line_necessary

#print axioms EndgameChess.Rules.KRKNineInner.rook_destination

#print axioms EndgameChess.Rules.KRKNineInner.rook_rays_necessary

#print axioms EndgameChess.Rules.KRKNineInner.canonical_rook_clear

#print axioms EndgameChess.Rules.KRKNineInner.clear_iff

#print axioms EndgameChess.Rules.KRKNineInner.kernel_nine_iff

#print axioms EndgameChess.Rules.KRKNineInner.kernel_exact_nine

#print axioms EndgameChess.Rules.KRKNineSecondLeft.no_nine

#print axioms EndgameChess.Rules.KRKNineNearDiagonal.no_nine

#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.corner_clear

#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.corner_region

#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.near_region

#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.second_region

#print axioms EndgameChess.Rules.KRKTenInner.near_guard_necessary

#print axioms EndgameChess.Rules.KRKTenInner.necessary

#print axioms EndgameChess.Rules.KRKTenInner.side_extra_clear

#print axioms EndgameChess.Rules.KRKTenInner.high_extra_clear

#print axioms EndgameChess.Rules.KRKTenInner.horizontal_clear

#print axioms EndgameChess.Rules.KRKTenInner.sufficient

#print axioms EndgameChess.Rules.KRKTenInner.clear_iff

#print axioms EndgameChess.Rules.KRKTenInner.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenInner.kernel_exact_ten

#print axioms EndgameChess.Rules.KRKTenInner.framed_clear_iff

#print axioms EndgameChess.Rules.KRKTenInteriorExact.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenInteriorExact.kernel_exact_ten

#print axioms EndgameChess.Rules.KRKNineEdge.clear_iff

#print axioms EndgameChess.Rules.KRKNineEdge.kernel_nine_iff

#print axioms EndgameChess.Rules.KRKTenEdge.nine_test_iff

#print axioms EndgameChess.Rules.KRKTenEdge.clear_iff

#print axioms EndgameChess.Rules.KRKTenEdge.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenGlobal.edge_clear_iff

#print axioms EndgameChess.Rules.KRKTenGlobal.kernel_ten_iff

#print axioms EndgameChess.Rules.KRKTenGlobal.region_live

#print axioms EndgameChess.Rules.KRKTenGlobal.kernel_exact_ten_iff

#print axioms EndgameChess.Rules.KRKCastleTen.inner_boundary_impossible

#print axioms EndgameChess.Rules.KRKCastleTen.bottom_interior_impossible

#print axioms EndgameChess.Rules.KRKCastleTen.nine_interior_impossible

#print axioms EndgameChess.Rules.KRKCastleTen.interior_covered

#print axioms EndgameChess.Rules.KRKCastleTen.king_bottom_no_ten

#print axioms EndgameChess.Rules.KRKCastleTen.queen_bottom_weak_corner

#print axioms EndgameChess.Rules.KRKCastleTen.home_king_no_ten

#print axioms EndgameChess.Rules.KRKCastleTen.home_queen_weak_corner

#print axioms EndgameChess.Rules.KRKCastleTen.castle_not_ten

#print axioms EndgameChess.Rules.KRKCastleTen.winning_entry_not_castle

#print axioms EndgameChess.Rules.KRKElevenEntry.ten_entry_move

#print axioms EndgameChess.Rules.KRKElevenSlots.nine_test_rank

#print axioms EndgameChess.Rules.KRKElevenSlots.region_rank

#print axioms EndgameChess.Rules.KRKElevenSlots.region_point

#print axioms EndgameChess.Rules.KRKElevenGeometry.entry_sufficient

#print axioms EndgameChess.Rules.KRKElevenGeometry.sufficient

#print axioms EndgameChess.Rules.KRKElevenGeometry.entry_necessary

#print axioms EndgameChess.Rules.KRKElevenGeometry.necessary

#print axioms EndgameChess.Rules.KRKElevenGeometry.kernel_eleven_iff

#print axioms EndgameChess.Rules.KRKElevenGeometry.frame_map

#print axioms EndgameChess.Rules.KRKElevenGeometry.king_step_clear

#print axioms EndgameChess.Rules.KRKElevenGeometry.rook_step_clear

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.clear_geometry

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.clear_kernel

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.entry_certificate

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.necessary

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKElevenPlyExact.necessary

#print axioms EndgameChess.Rules.KRKElevenPlyExact.rule_eleven_iff

#print axioms EndgameChess.Rules.KRKElevenPlyExact.strong_twelve_eleven

#print axioms EndgameChess.Rules.KRKElevenPlyExact.weak_thirteen_twelve

#print axioms EndgameChess.Rules.KRKElevenPlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKElevenPlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.after_weak_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.child_eleven_certificate

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.necessary

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_hold_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyExact.necessary

#print axioms EndgameChess.Rules.KRKTwelvePlyExact.rule_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelvePlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKTwelvePlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKTwelveGeometry.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveGeometry.strong_twelve_eleven

#print axioms EndgameChess.Rules.KRKTwelveGeometry.weak_thirteen_twelve

#print axioms EndgameChess.Rules.KRKTwelveGeometry.ten_region_depth

#print axioms EndgameChess.Rules.KRKTwelveGeometry.eleven_weak_depth

#print axioms EndgameChess.Rules.KRKTwelveGeometry.frame_map

#print axioms EndgameChess.Rules.KRKElevenNearBoundary.upper_necessary

#print axioms EndgameChess.Rules.KRKElevenNearBoundary.two_four_not_clear

#print axioms EndgameChess.Rules.KRKElevenNearBoundary.upper_sufficient

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.bad_neighbour_covered

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.prison

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_necessary

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.necessary

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_clear

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.sufficient

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveDeepExact.central_escape

#print axioms EndgameChess.Rules.KRKTwelveDeepExact.corner_target

#print axioms EndgameChess.Rules.KRKTwelveDeepExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveDeepExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKElevenNearStrip.region_shape

#print axioms EndgameChess.Rules.KRKElevenNearStrip.global_region_iff

#print axioms EndgameChess.Rules.KRKElevenNearStrip.rook_line_necessary

#print axioms EndgameChess.Rules.KRKElevenNearStrip.rook_destination

#print axioms EndgameChess.Rules.KRKElevenNearStrip.clear_iff

#print axioms EndgameChess.Rules.KRKElevenNearStrip.kernel_eleven_iff

#print axioms EndgameChess.Rules.KRKElevenNearStrip.kernel_exact_eleven

#print axioms EndgameChess.Rules.KRKElevenNearStrip.framed_clear_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.near_eight_region

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.near_nine_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_ten_region

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_eight_region

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_nine_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.second_ten_region

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.prison

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.row_four_necessary

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.upper_necessary

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.protected_two_four_no_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.candidate_necessary

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.row_four_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_exact_twelve

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.inner_file_bound

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_rank_bound

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_eight

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_upper_low_rook

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_nine

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.ten_high_near_cover

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_ten_high_rook_rank

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_two_not_eleven

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_one_not_eleven

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_eight

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_nine

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_ten_high_rook_rank

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_zero_not_eleven

#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.near_eight

#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.middle_eight

#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.second_eight

#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.ten_edge_region

#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.edge_eleven

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_two_no_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.protected_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_zero_no_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eight

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_ten

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_eleven

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_ten

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eleven

#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.high_eleven

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.opposition_clear

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.necessary

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.sufficient

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveCentralExact.framed_clear_iff

#print axioms EndgameChess.Rules.KRKElevenInner.horizontal_shape

#print axioms EndgameChess.Rules.KRKElevenInner.global_region_iff

#print axioms EndgameChess.Rules.KRKElevenInner.king_points_iff

#print axioms EndgameChess.Rules.KRKElevenInner.rook_line_necessary

#print axioms EndgameChess.Rules.KRKElevenInner.rook_destination

#print axioms EndgameChess.Rules.KRKElevenInner.rook_rays_necessary

#print axioms EndgameChess.Rules.KRKElevenInner.canonical_rook_clear

#print axioms EndgameChess.Rules.KRKElevenInner.clear_iff

#print axioms EndgameChess.Rules.KRKElevenInner.kernel_eleven_iff

#print axioms EndgameChess.Rules.KRKElevenInner.kernel_exact_eleven

#print axioms EndgameChess.Rules.KRKElevenInner.framed_clear_iff

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.prison

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_two_necessary

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.protected_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_three_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_three_necessary

#print axioms EndgameChess.Rules.KRKTwelveNearStrip.upper_low_no_clear

#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.low_ten

#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.low_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.middle_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.necessary

#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.sufficient

#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.eight_region_subset

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.low_near_ten

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_second_ten

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.high_near_ten

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_low_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_near_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_middle_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_lower_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_inner_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_inner_eleven

#print axioms EndgameChess.Rules.KRKTwelveNearUpper.blocked_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveNearUpper.necessary

#print axioms EndgameChess.Rules.KRKTwelveNearUpper.ten_clear_subset

#print axioms EndgameChess.Rules.KRKTwelveNearUpper.protected_clear

#print axioms EndgameChess.Rules.KRKTwelveNearUpper.sufficient

#print axioms EndgameChess.Rules.KRKTwelveNearExact.row_two_clear

#print axioms EndgameChess.Rules.KRKTwelveNearExact.necessary

#print axioms EndgameChess.Rules.KRKTwelveNearExact.sufficient

#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveNearExact.fresh_iff

#print axioms EndgameChess.Rules.KRKTwelveNearExact.framed_clear_iff

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_ten_high_rook_rank

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_five_one_not_eleven

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_low_row_not_eight

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_not_eight

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_eight

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_nine

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_low_row_not_nine

#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_one_three_high_rook_not_eleven

#print axioms EndgameChess.Rules.KRKTwelveInner.near_guard_prison

#print axioms EndgameChess.Rules.KRKTwelveInner.prison

#print axioms EndgameChess.Rules.KRKTwelveInner.same_file_rook_below

#print axioms EndgameChess.Rules.KRKTwelveInner.zero_five_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInner.one_five_high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInner.near_guard_sharp

#print axioms EndgameChess.Rules.KRKTwelveInner.ten_clear_subset

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.clear

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.five_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_height_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.sufficient

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.low_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerSide.necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerSide.sufficient

#print axioms EndgameChess.Rules.KRKTwelveInnerSide.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerSide.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerSide.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.clear

#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.kernel_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_second_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_corner_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.low_second

#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_second

#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_near

#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.sufficient

#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_eight

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_corner_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_near_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.second_outer_ten

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.sufficient

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.upper_three_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.two_five_four_no_clear

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.five_necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.clear

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.necessary

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.sufficient

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKTwelveInnerExact.framed_clear_iff

#print axioms EndgameChess.Rules.KRKTwelveInteriorExact.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveInteriorExact.kernel_exact_twelve

#print axioms EndgameChess.Rules.KRKElevenEdge.clear_iff

#print axioms EndgameChess.Rules.KRKElevenEdge.kernel_eleven_iff

#print axioms EndgameChess.Rules.KRKTwelveEdge.eleven_test_iff

#print axioms EndgameChess.Rules.KRKTwelveEdge.clear_iff

#print axioms EndgameChess.Rules.KRKTwelveEdge.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveGlobal.edge_clear_iff

#print axioms EndgameChess.Rules.KRKTwelveGlobal.kernel_twelve_iff

#print axioms EndgameChess.Rules.KRKTwelveGlobal.region_live

#print axioms EndgameChess.Rules.KRKTwelveGlobal.kernel_exact_twelve_iff

#print axioms EndgameChess.Rules.KRKCastleTwelve.eleven_interior_impossible

#print axioms EndgameChess.Rules.KRKCastleTwelve.interior_covered

#print axioms EndgameChess.Rules.KRKCastleTwelve.king_bottom_no_twelve

#print axioms EndgameChess.Rules.KRKCastleTwelve.queen_bottom_weak_corner

#print axioms EndgameChess.Rules.KRKCastleTwelve.home_king_no_twelve

#print axioms EndgameChess.Rules.KRKCastleTwelve.home_queen_weak_corner

#print axioms EndgameChess.Rules.KRKCastleTwelve.castle_not_twelve

#print axioms EndgameChess.Rules.KRKCastleTwelve.winning_entry_not_castle

#print axioms EndgameChess.Rules.KRKThirteenEntry.twelve_entry_move

#print axioms EndgameChess.Rules.KRKThirteenSlots.region_point

#print axioms EndgameChess.Rules.KRKThirteenGeometry.entry_sufficient

#print axioms EndgameChess.Rules.KRKThirteenGeometry.sufficient

#print axioms EndgameChess.Rules.KRKThirteenGeometry.entry_necessary

#print axioms EndgameChess.Rules.KRKThirteenGeometry.necessary

#print axioms EndgameChess.Rules.KRKThirteenGeometry.kernel_thirteen_iff

#print axioms EndgameChess.Rules.KRKThirteenGeometry.frame_map

#print axioms EndgameChess.Rules.KRKThirteenGeometry.king_step_clear

#print axioms EndgameChess.Rules.KRKThirteenGeometry.rook_step_clear

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.clear_geometry

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.clear_kernel

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.entry_certificate

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.necessary

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.necessary

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.rule_thirteen_iff

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.strong_fourteen_thirteen

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.weak_fifteen_fourteen

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKThirteenPlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.after_weak_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.child_thirteen_certificate

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.necessary

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.sufficient

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_force_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_actual_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_hold_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_draw_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyExact.necessary

#print axioms EndgameChess.Rules.KRKFourteenPlyExact.rule_fourteen_iff

#print axioms EndgameChess.Rules.KRKFourteenPlyExact.distance_cases

#print axioms EndgameChess.Rules.KRKFourteenPlyExact.high_clock_exact_distance

#print axioms EndgameChess.Rules.KRKFourteenGeometry.kernel_fourteen_iff

#print axioms EndgameChess.Rules.KRKFourteenGeometry.strong_fourteen_thirteen

#print axioms EndgameChess.Rules.KRKFourteenGeometry.weak_fifteen_fourteen

#print axioms EndgameChess.Rules.KRKFourteenGeometry.twelve_region_depth

#print axioms EndgameChess.Rules.KRKFourteenGeometry.thirteen_weak_depth

#print axioms EndgameChess.Rules.KRKFourteenGeometry.thirteen_deep_corner

#print axioms EndgameChess.Rules.KRKFourteenGeometry.frame_map

#print axioms EndgameChess.Rules.KRKFourteenDeep.bad_neighbour_covered

#print axioms EndgameChess.Rules.KRKFourteenDeep.central_three_no_clear

#print axioms EndgameChess.Rules.KRKFourteenDeep.central_no_clear

#print axioms EndgameChess.Rules.KRKFourteenDeep.kernel_central_no_fourteen

#print axioms EndgameChess.Rules.KRKFourteenDeepStrip.prison

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.second_region_iff

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.near_region_iff

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.central_region_iff

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.second_entry_necessary

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.central_four_four_no_thirteen

#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.near_upper_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.near_corner_no_clear

#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.belt_no_clear

#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.deep_corner_necessary

#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.kernel_deep_corner_necessary

#print axioms EndgameChess.Rules.KRKFourteenSecondCorner.prison

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerEntries.opposition_clear

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerEntries.kernel_exact_fourteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_zero_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_two_file_two_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_three_four_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_four_three_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_three_four_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.inner_diagonal_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.necessary

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.sufficient

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_fourteen_iff

#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_exact_fourteen

#print axioms EndgameChess.Rules.KRKFourteenDeepExact.fresh_iff

#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_fourteen_iff

#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen_iff

#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.region_shape

#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.rook_line_necessary

#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.rook_destination

#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.clear_iff

#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.kernel_thirteen_iff

#print axioms EndgameChess.Rules.KRKFourteenCentralEntries.opposition_clear

#print axioms EndgameChess.Rules.KRKFourteenCentralEntries.kernel_exact_fourteen

#print axioms EndgameChess.Rules.KRKFourteenCentralPrison.legal_upper

#print axioms EndgameChess.Rules.KRKFourteenCentralPrison.prison

#print axioms EndgameChess.Rules.KRKFourteenCentralUpperEntries.upper_one_clear

#print axioms EndgameChess.Rules.KRKFourteenCentralUpperEntries.kernel_upper_one_exact_fourteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.second_three_four_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.second_upper_row_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_three_four_file_two_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_three_three_row_four_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_low_rook_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_three_high_no_thirteen

#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.upper_two_above_no_clear

#print axioms EndgameChess.Rules.KRKFourteenCentralNecessary.necessary

#print axioms EndgameChess.Rules.KRKFourteenCentralUpperZero.low_second_twelve

#print axioms EndgameChess.Rules.KRKFourteenCentralUpperZero.clear

#print axioms EndgameChess.Rules.KRKFourteenCentralUpperTwo.clear

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.sufficient

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.clear_iff

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.fresh_iff

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.kernel_fourteen_iff

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.kernel_exact_fourteen

#print axioms EndgameChess.Rules.KRKFourteenCentralExact.framed_clear_iff

#print axioms EndgameChess.Rules.KRKThirteenNearRook.rook_line_necessary

#print axioms EndgameChess.Rules.KRKThirteenNearRook.rook_destination

#print axioms EndgameChess.Rules.KRKThirteenNearStrip.region_shape

#print axioms EndgameChess.Rules.KRKThirteenNearStrip.clear_iff

#print axioms EndgameChess.Rules.KRKThirteenNearStrip.kernel_thirteen_iff

#print axioms EndgameChess.Rules.KRKThirteenNearStrip.kernel_exact_thirteen

#print axioms EndgameChess.Rules.KRKThirteenInnerRook.high_destination

#print axioms EndgameChess.Rules.KRKThirteenInnerRook.rook_line_necessary

-- Complete EC-T0049 public-theorem coverage.
#print axioms EndgameChess.Rules.KRKEightCentralStrip.not_clear
#print axioms EndgameChess.Rules.KRKEightCentralStrip.kernel_no_eight
#print axioms EndgameChess.Rules.KRKEightNearStrip.no_upper_king
#print axioms EndgameChess.Rules.KRKEightNearStrip.file_one_requires_row_three
#print axioms EndgameChess.Rules.KRKEightNearStrip.row_three_necessary
#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKSevenCorner.frame_f
#print axioms EndgameChess.Rules.KRKSevenCorner.frame_r
#print axioms EndgameChess.Rules.KRKSevenCorner.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_properties
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_rook_clear
#print axioms EndgameChess.Rules.KRKSevenInner.swap_clear_iff
#print axioms EndgameChess.Rules.KRKSevenNear.king_far
#print axioms EndgameChess.Rules.KRKSevenNear.slot_properties
#print axioms EndgameChess.Rules.KRKSevenNear.diagonal_live
#print axioms EndgameChess.Rules.KRKSevenNear.slot_live
#print axioms EndgameChess.Rules.KRKSevenNear.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenNear.low_reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.side_reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.high_reach_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.frame_f
#print axioms EndgameChess.Rules.KRKSevenSecond.frame_r
#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve

-- KQK and shared lone-king interfaces (class proof in progress).
#print axioms EndgameChess.Rules.LoneKing.board_some
#print axioms EndgameChess.Rules.LoneKing.board_none
#print axioms EndgameChess.Rules.LoneKing.board_sk
#print axioms EndgameChess.Rules.LoneKing.board_xs
#print axioms EndgameChess.Rules.LoneKing.board_wk
#print axioms EndgameChess.Rules.LoneKing.king_at
#print axioms EndgameChess.Rules.LoneKing.attacked_iff
#print axioms EndgameChess.Rules.LoneKing.strong_check
#print axioms EndgameChess.Rules.LoneKing.weak_check
#print axioms EndgameChess.Rules.LoneKing.weak_motion
#print axioms EndgameChess.Rules.LoneKing.weak_cases
#print axioms EndgameChess.Rules.LoneKing.safe_reply
#print axioms EndgameChess.Rules.LoneKing.unprotected_capture
#print axioms EndgameChess.Rules.LoneKing.force_weak_safe
#print axioms EndgameChess.Rules.KQK.between_self
#print axioms EndgameChess.Rules.KQK.between_end
#print axioms EndgameChess.Rules.KQK.path_clear
#print axioms EndgameChess.Rules.KQK.queen_attacks
#print axioms EndgameChess.Rules.KQK.rook_sees_queen
#print axioms EndgameChess.Rules.KQK.strong_check
#print axioms EndgameChess.Rules.KQK.weak_check
#print axioms EndgameChess.Rules.KQK.safe_reply
#print axioms EndgameChess.Rules.KQK.rank_reply
#print axioms EndgameChess.Rules.KQK.force_weak_safe
#print axioms EndgameChess.Rules.KQK.no_weak_force
#print axioms EndgameChess.Rules.KQK.unsafe_weak_no_forcing
#print axioms EndgameChess.Rules.KQK.strong_reply
#print axioms EndgameChess.Rules.KQK.edge_reply_exists
#print axioms EndgameChess.Rules.KQK.edge_reply
#print axioms EndgameChess.Rules.KQK.toward_step
#print axioms EndgameChess.Rules.KQK.corner_prison_bound
#print axioms EndgameChess.Rules.KQK.outside_corridor_bound
#print axioms EndgameChess.Rules.KQK.outside_corridor_weak_bound
#print axioms EndgameChess.Rules.KQK.top_left_corridor_bound
#print axioms EndgameChess.Rules.KQK.top_right_corridor_bound
#print axioms EndgameChess.Rules.KQK.corridor_bound
#print axioms EndgameChess.Rules.KQK.framed_corridor_bound
#print axioms EndgameChess.Rules.KQK.corner_prison_fifteen
#print axioms EndgameChess.Rules.KQK.edge_wall_bound
#print axioms EndgameChess.Rules.KQK.edge_wall_twenty_five
#print axioms EndgameChess.Rules.KQK.edge_wall_weak_bound
#print axioms EndgameChess.Rules.KQK.corner_example_bound
#print axioms EndgameChess.Rules.KQK.stalemate_example_no_force
#print axioms EndgameChess.Rules.KQK.shadow_example_bound
#print axioms EndgameChess.Rules.KQK.blocked_entry_example_bound
#print axioms EndgameChess.Rules.KQK.staircase_example_bound
#print axioms EndgameChess.Rules.KQK.horizontal_entry_example_bound
#print axioms EndgameChess.Rules.KQK.top_left_entry_example_bound
#print axioms EndgameChess.Rules.KQK.corner_evacuation_example_bound
#print axioms EndgameChess.Rules.KQK.direct_evacuation_stalemate
#print axioms EndgameChess.Rules.KQK.unframe_bound
#print axioms EndgameChess.Rules.KQK.framed_edge_wall_bound
#print axioms EndgameChess.Rules.KQK.framed_prison_bound
#print axioms EndgameChess.Rules.KQK.framed_edge_wall_weak_bound
#print axioms EndgameChess.Rules.KQK.framed_prison_weak_bound
#print axioms EndgameChess.Rules.KQK.between_near
#print axioms EndgameChess.Rules.KQK.near_sees
#print axioms EndgameChess.Rules.KQK.queen_distant_of_not_check
#print axioms EndgameChess.Rules.KQK.not_sees_of_not_line
#print axioms EndgameChess.Rules.KQK.edge_mated
#print axioms EndgameChess.Rules.KQK.sees_ray
#print axioms EndgameChess.Rules.KQK.interior_escape_geometry
#print axioms EndgameChess.Rules.KQK.interior_reply_exists
#print axioms EndgameChess.Rules.KQK.stalemate_boundary
#print axioms EndgameChess.Rules.KQK.queen_move
#print axioms EndgameChess.Rules.KQK.king_move
#print axioms EndgameChess.Rules.KQK.weak_move
#print axioms EndgameChess.Rules.KQK.prison_reply_exists
#print axioms EndgameChess.Rules.KQK.prison_reply
#print axioms EndgameChess.Rules.KQK.prison_bound
#print axioms EndgameChess.Rules.KQK.prison_weak_bound
#print axioms EndgameChess.Rules.KQK.framed_shadow_strong_bound
#print axioms EndgameChess.Rules.KQK.framed_shadow_weak_bound
#print axioms EndgameChess.Rules.KQK.vertical_shadow_entry
#print axioms EndgameChess.Rules.KQK.two_file_entry_bound
#print axioms EndgameChess.Rules.KQK.blocked_file_entry_bound
#print axioms EndgameChess.Rules.KQK.horizontal_alignment_entry
#print axioms EndgameChess.Rules.KQK.framed_vertical_shadow_entry
#print axioms EndgameChess.Rules.KQK.framed_blocked_file_entry
#print axioms EndgameChess.Rules.KQK.shadow_exit_bound
#print axioms EndgameChess.Rules.KQK.shadow_weak_bound
#print axioms EndgameChess.Rules.KQK.shadow_weak_fifty_two
#print axioms EndgameChess.Rules.KQK.shadow_strong_bound
#print axioms EndgameChess.Rules.KQK.sum_far
#print axioms EndgameChess.Rules.KQK.shadow_reply_exists
#print axioms EndgameChess.Rules.KQK.shadow_reply
#print axioms EndgameChess.Rules.KQK.staircase_bound
#print axioms EndgameChess.Rules.KQK.staircase_eighty_one
#print axioms EndgameChess.Rules.KQK.framed_staircase_bound
#print axioms EndgameChess.Rules.KQK.sees_split
#print axioms EndgameChess.Rules.KQK.QueenSym.sees_iff
#print axioms EndgameChess.Rules.KQK.bound_transport
-- New non-frozen executable KRK extraction witnesses (standard-axiom audit).
#print axioms EndgameChess.Rules.KRKExecutable.rookWaitDestination_sound
#print axioms EndgameChess.Rules.KRKExecutable.rankAdvanceDestination_sound
#print axioms EndgameChess.Rules.KRKExecutable.prepNext_sound
#print axioms EndgameChess.Rules.KRKExecutable.readyUpperDestination_sound
#print axioms EndgameChess.Rules.KRKExecutable.wallNext_sound
#print axioms EndgameChess.Rules.KRKExecutable.lowerBandTempo_sound
