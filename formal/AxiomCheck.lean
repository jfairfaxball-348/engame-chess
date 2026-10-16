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
