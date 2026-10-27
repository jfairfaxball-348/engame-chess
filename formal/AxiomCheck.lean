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
