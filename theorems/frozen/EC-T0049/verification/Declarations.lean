import EndgameChess
import EndgameChess.Rules.KRKCanonicalSlots
import EndgameChess.Rules.KRKCastleEight
import EndgameChess.Rules.KRKCastleFour
import EndgameChess.Rules.KRKCastleSix
import EndgameChess.Rules.KRKCastleTen
import EndgameChess.Rules.KRKCastleTwelve
import EndgameChess.Rules.KRKCentralWeakBand
import EndgameChess.Rules.KRKCornerSlotBarriers
import EndgameChess.Rules.KRKCornerSlotPrefix
import EndgameChess.Rules.KRKCornerWeakBand
import EndgameChess.Rules.KRKDeadline.Definitions
import EndgameChess.Rules.KRKDeadline.Necessary
import EndgameChess.Rules.KRKDistanceParity
import EndgameChess.Rules.KRKEdgeDepth
import EndgameChess.Rules.KRKEdgeDepthHistory
import EndgameChess.Rules.KRKEightCentralStrip
import EndgameChess.Rules.KRKEightCentralStripHolding
import EndgameChess.Rules.KRKEightDiagonalEntries
import EndgameChess.Rules.KRKEightEdge
import EndgameChess.Rules.KRKEightGeometry
import EndgameChess.Rules.KRKEightGlobal
import EndgameChess.Rules.KRKEightInner
import EndgameChess.Rules.KRKEightInterior
import EndgameChess.Rules.KRKEightInteriorExact
import EndgameChess.Rules.KRKEightInteriorHolding
import EndgameChess.Rules.KRKEightNearStrip
import EndgameChess.Rules.KRKEightPlyExact
import EndgameChess.Rules.KRKEightPlyHistory
import EndgameChess.Rules.KRKEightPrefix
import EndgameChess.Rules.KRKEightStrip
import EndgameChess.Rules.KRKElevenEdge
import EndgameChess.Rules.KRKElevenEdgeBoundary
import EndgameChess.Rules.KRKElevenEntry
import EndgameChess.Rules.KRKElevenGeometry
import EndgameChess.Rules.KRKElevenInner
import EndgameChess.Rules.KRKElevenNearBoundary
import EndgameChess.Rules.KRKElevenNearStrip
import EndgameChess.Rules.KRKElevenPlyExact
import EndgameChess.Rules.KRKElevenPlyHistory
import EndgameChess.Rules.KRKElevenSlots
import EndgameChess.Rules.KRKFiveCornerEntries
import EndgameChess.Rules.KRKFiveGeometry
import EndgameChess.Rules.KRKFiveMiddle
import EndgameChess.Rules.KRKFiveNear
import EndgameChess.Rules.KRKFivePlyExact
import EndgameChess.Rules.KRKFivePlyHistory
import EndgameChess.Rules.KRKFiveWeakPrefix
import EndgameChess.Rules.KRKFourGeometry
import EndgameChess.Rules.KRKFourPlyCorner
import EndgameChess.Rules.KRKFourPlyCornerKernel
import EndgameChess.Rules.KRKFourPlyEscape
import EndgameChess.Rules.KRKFourPlyExact
import EndgameChess.Rules.KRKFourPlyInterior
import EndgameChess.Rules.KRKFourPlyMiddle
import EndgameChess.Rules.KRKFourPlyNearCorner
import EndgameChess.Rules.KRKFourPlyNearKernel
import EndgameChess.Rules.KRKFourPlySecond
import EndgameChess.Rules.KRKFourSlots
import EndgameChess.Rules.KRKFourteenCentralBounds
import EndgameChess.Rules.KRKFourteenCentralEntries
import EndgameChess.Rules.KRKFourteenCentralExact
import EndgameChess.Rules.KRKFourteenCentralNecessary
import EndgameChess.Rules.KRKFourteenCentralPrison
import EndgameChess.Rules.KRKFourteenCentralUpperEntries
import EndgameChess.Rules.KRKFourteenCentralUpperTwo
import EndgameChess.Rules.KRKFourteenCentralUpperZero
import EndgameChess.Rules.KRKFourteenDeep
import EndgameChess.Rules.KRKFourteenDeepExact
import EndgameChess.Rules.KRKFourteenDeepStrip
import EndgameChess.Rules.KRKFourteenDeepStripHolding
import EndgameChess.Rules.KRKFourteenGeometry
import EndgameChess.Rules.KRKFourteenPlyExact
import EndgameChess.Rules.KRKFourteenPlyHistory
import EndgameChess.Rules.KRKFourteenSecondCorner
import EndgameChess.Rules.KRKFourteenSecondCornerBounds
import EndgameChess.Rules.KRKFourteenSecondCornerEntries
import EndgameChess.Rules.KRKFourteenSecondCornerExact
import EndgameChess.Rules.KRKFrameBound
import EndgameChess.Rules.KRKFramedHistory
import EndgameChess.Rules.KRKFramedPrefix
import EndgameChess.Rules.KRKGeometricSymmetry
import EndgameChess.Rules.KRKGlobalWeakBand
import EndgameChess.Rules.KRKImmediate
import EndgameChess.Rules.KRKImmediateHistory
import EndgameChess.Rules.KRKInteriorHolding
import EndgameChess.Rules.KRKInteriorLowerBound
import EndgameChess.Rules.KRKLastReply
import EndgameChess.Rules.KRKLastReplyHistory
import EndgameChess.Rules.KRKLastReplyKernel
import EndgameChess.Rules.KRKLastReplyKey
import EndgameChess.Rules.KRKMateGeometry
import EndgameChess.Rules.KRKMatingMove
import EndgameChess.Rules.KRKNativeFrame
import EndgameChess.Rules.KRKNearKingBarrier
import EndgameChess.Rules.KRKNearSlotBarriers
import EndgameChess.Rules.KRKNearWeakBand
import EndgameChess.Rules.KRKNineEdge
import EndgameChess.Rules.KRKNineEntry
import EndgameChess.Rules.KRKNineGeometry
import EndgameChess.Rules.KRKNineInner
import EndgameChess.Rules.KRKNineInnerBoundary
import EndgameChess.Rules.KRKNineMiddleLow
import EndgameChess.Rules.KRKNineNearDiagonal
import EndgameChess.Rules.KRKNineNearStrip
import EndgameChess.Rules.KRKNineNearStripHistory
import EndgameChess.Rules.KRKNinePlyExact
import EndgameChess.Rules.KRKNinePlyHistory
import EndgameChess.Rules.KRKNineSecondBoundary
import EndgameChess.Rules.KRKNineSecondLeft
import EndgameChess.Rules.KRKNineSlots
import EndgameChess.Rules.KRKNineUpperEntries
import EndgameChess.Rules.KRKOppositionHistory
import EndgameChess.Rules.KRKOppositionPrefix
import EndgameChess.Rules.KRKOrdinaryEntry
import EndgameChess.Rules.KRKRookRayBarriers
import EndgameChess.Rules.KRKSecondOppositionHistory
import EndgameChess.Rules.KRKSecondOppositionPrefix
import EndgameChess.Rules.KRKSecondSlotPrefix
import EndgameChess.Rules.KRKSecondStrongSlots
import EndgameChess.Rules.KRKSecondWeakBand
import EndgameChess.Rules.KRKSecondWestHistory
import EndgameChess.Rules.KRKSevenCorner
import EndgameChess.Rules.KRKSevenEntry
import EndgameChess.Rules.KRKSevenGeometry
import EndgameChess.Rules.KRKSevenInner
import EndgameChess.Rules.KRKSevenMiddle
import EndgameChess.Rules.KRKSevenNear
import EndgameChess.Rules.KRKSevenPlyExact
import EndgameChess.Rules.KRKSevenPlyHistory
import EndgameChess.Rules.KRKSevenPrefix
import EndgameChess.Rules.KRKSevenReach
import EndgameChess.Rules.KRKSevenSecond
import EndgameChess.Rules.KRKSevenSlots
import EndgameChess.Rules.KRKSixCorner
import EndgameChess.Rules.KRKSixGeometry
import EndgameChess.Rules.KRKSixGlobal
import EndgameChess.Rules.KRKSixInterior
import EndgameChess.Rules.KRKSixInteriorHolding
import EndgameChess.Rules.KRKSixInwardCorner
import EndgameChess.Rules.KRKSixMiddle
import EndgameChess.Rules.KRKSixNear
import EndgameChess.Rules.KRKSixPlyExact
import EndgameChess.Rules.KRKSixPlyHistory
import EndgameChess.Rules.KRKSixSecond
import EndgameChess.Rules.KRKSlotPrefix
import EndgameChess.Rules.KRKStrongPrefix
import EndgameChess.Rules.KRKTenCentralStrip
import EndgameChess.Rules.KRKTenCentralStripHolding
import EndgameChess.Rules.KRKTenEdge
import EndgameChess.Rules.KRKTenGeometry
import EndgameChess.Rules.KRKTenGlobal
import EndgameChess.Rules.KRKTenInner
import EndgameChess.Rules.KRKTenInterior
import EndgameChess.Rules.KRKTenInteriorExact
import EndgameChess.Rules.KRKTenInteriorHolding
import EndgameChess.Rules.KRKTenNearStrip
import EndgameChess.Rules.KRKTenPlyExact
import EndgameChess.Rules.KRKTenPlyHistory
import EndgameChess.Rules.KRKTenSecondCorner
import EndgameChess.Rules.KRKTenSecondCornerHolding
import EndgameChess.Rules.KRKThirteenCentralStrip
import EndgameChess.Rules.KRKThirteenEntry
import EndgameChess.Rules.KRKThirteenGeometry
import EndgameChess.Rules.KRKThirteenInnerRook
import EndgameChess.Rules.KRKThirteenInteriorBarriers
import EndgameChess.Rules.KRKThirteenNearRook
import EndgameChess.Rules.KRKThirteenNearStrip
import EndgameChess.Rules.KRKThirteenPlyExact
import EndgameChess.Rules.KRKThirteenPlyHistory
import EndgameChess.Rules.KRKThirteenSlots
import EndgameChess.Rules.KRKThreePly
import EndgameChess.Rules.KRKThreePlyCorner
import EndgameChess.Rules.KRKThreePlyExact
import EndgameChess.Rules.KRKThreePlyHistory
import EndgameChess.Rules.KRKThreePlyMiddle
import EndgameChess.Rules.KRKThreePlyNearCorner
import EndgameChess.Rules.KRKTwelveCentralEntries
import EndgameChess.Rules.KRKTwelveCentralExact
import EndgameChess.Rules.KRKTwelveCentralOppositionEntries
import EndgameChess.Rules.KRKTwelveCentralStrip
import EndgameChess.Rules.KRKTwelveCentralUpper
import EndgameChess.Rules.KRKTwelveCentralUpperEntries
import EndgameChess.Rules.KRKTwelveDeepExact
import EndgameChess.Rules.KRKTwelveEdge
import EndgameChess.Rules.KRKTwelveGeometry
import EndgameChess.Rules.KRKTwelveGlobal
import EndgameChess.Rules.KRKTwelveInner
import EndgameChess.Rules.KRKTwelveInnerBoundaryEntries
import EndgameChess.Rules.KRKTwelveInnerDiagonal
import EndgameChess.Rules.KRKTwelveInnerDiagonalExact
import EndgameChess.Rules.KRKTwelveInnerExact
import EndgameChess.Rules.KRKTwelveInnerFileOne
import EndgameChess.Rules.KRKTwelveInnerHigh
import EndgameChess.Rules.KRKTwelveInnerHighExact
import EndgameChess.Rules.KRKTwelveInnerOuter
import EndgameChess.Rules.KRKTwelveInnerSide
import EndgameChess.Rules.KRKTwelveInnerUpperBoundary
import EndgameChess.Rules.KRKTwelveInnerUpperEntries
import EndgameChess.Rules.KRKTwelveInnerUpperFive
import EndgameChess.Rules.KRKTwelveInnerUpperFour
import EndgameChess.Rules.KRKTwelveInteriorExact
import EndgameChess.Rules.KRKTwelveNearExact
import EndgameChess.Rules.KRKTwelveNearFileEntries
import EndgameChess.Rules.KRKTwelveNearFileOne
import EndgameChess.Rules.KRKTwelveNearNewEntries
import EndgameChess.Rules.KRKTwelveNearStrip
import EndgameChess.Rules.KRKTwelveNearUpper
import EndgameChess.Rules.KRKTwelvePlyExact
import EndgameChess.Rules.KRKTwelvePlyHistory
import EndgameChess.Rules.KRKTwelveSecondCorner
import EndgameChess.Rules.KRKVerticalNearSlotBarriers
import EndgameChess.Rules.KRKWeakBranch
import EndgameChess.Rules.KRKWeakPrefixEntry
#check @EndgameChess.Rules.KRKCanonicalSlots.valid_bounds
#print axioms EndgameChess.Rules.KRKCanonicalSlots.valid_bounds
#check @EndgameChess.Rules.KRKCanonicalSlots.last_catalogue_iff
#print axioms EndgameChess.Rules.KRKCanonicalSlots.last_catalogue_iff
#check @EndgameChess.Rules.KRKCanonicalSlots.slot_last
#print axioms EndgameChess.Rules.KRKCanonicalSlots.slot_last
#check @EndgameChess.Rules.KRKCanonicalSlots.king_far
#print axioms EndgameChess.Rules.KRKCanonicalSlots.king_far
#check @EndgameChess.Rules.KRKCanonicalSlots.reply_distance
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_distance
#check @EndgameChess.Rules.KRKCanonicalSlots.reply_far
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_far
#check @EndgameChess.Rules.KRKCanonicalSlots.region_off_reply
#print axioms EndgameChess.Rules.KRKCanonicalSlots.region_off_reply
#check @EndgameChess.Rules.KRKCanonicalSlots.reply_step
#print axioms EndgameChess.Rules.KRKCanonicalSlots.reply_step
#check @EndgameChess.Rules.KRKCanonicalSlots.region_off_weak
#print axioms EndgameChess.Rules.KRKCanonicalSlots.region_off_weak
#check @EndgameChess.Rules.KRKCastleEight.seven_bottom_interior
#print axioms EndgameChess.Rules.KRKCastleEight.seven_bottom_interior
#check @EndgameChess.Rules.KRKCastleEight.above_covered
#print axioms EndgameChess.Rules.KRKCastleEight.above_covered
#check @EndgameChess.Rules.KRKCastleEight.rank_prison
#print axioms EndgameChess.Rules.KRKCastleEight.rank_prison
#check @EndgameChess.Rules.KRKCastleEight.king_bottom_no_eight
#print axioms EndgameChess.Rules.KRKCastleEight.king_bottom_no_eight
#check @EndgameChess.Rules.KRKCastleEight.queen_bottom_weak_corner
#print axioms EndgameChess.Rules.KRKCastleEight.queen_bottom_weak_corner
#check @EndgameChess.Rules.KRKCastleEight.frame_map
#print axioms EndgameChess.Rules.KRKCastleEight.frame_map
#check @EndgameChess.Rules.KRKCastleEight.home_king_no_eight
#print axioms EndgameChess.Rules.KRKCastleEight.home_king_no_eight
#check @EndgameChess.Rules.KRKCastleEight.home_queen_weak_corner
#print axioms EndgameChess.Rules.KRKCastleEight.home_queen_weak_corner
#check @EndgameChess.Rules.KRKCastleEight.castle_not_eight
#print axioms EndgameChess.Rules.KRKCastleEight.castle_not_eight
#check @EndgameChess.Rules.KRKCastleEight.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKCastleEight.winning_entry_not_castle
#check @EndgameChess.Rules.KRKCastleFour.queen_geometry
#print axioms EndgameChess.Rules.KRKCastleFour.queen_geometry
#check @EndgameChess.Rules.KRKCastleFour.king_geometry
#print axioms EndgameChess.Rules.KRKCastleFour.king_geometry
#check @EndgameChess.Rules.KRKCastleFour.king_square
#print axioms EndgameChess.Rules.KRKCastleFour.king_square
#check @EndgameChess.Rules.KRKCastleFour.rook_square
#print axioms EndgameChess.Rules.KRKCastleFour.rook_square
#check @EndgameChess.Rules.KRKCastleFour.castle_not_four
#print axioms EndgameChess.Rules.KRKCastleFour.castle_not_four
#check @EndgameChess.Rules.KRKCastleFour.four_entry_move
#print axioms EndgameChess.Rules.KRKCastleFour.four_entry_move
#check @EndgameChess.Rules.KRKCastleSix.five_depth_zero
#print axioms EndgameChess.Rules.KRKCastleSix.five_depth_zero
#check @EndgameChess.Rules.KRKCastleSix.interior_covered
#print axioms EndgameChess.Rules.KRKCastleSix.interior_covered
#check @EndgameChess.Rules.KRKCastleSix.rank_prison
#print axioms EndgameChess.Rules.KRKCastleSix.rank_prison
#check @EndgameChess.Rules.KRKCastleSix.corner_prison
#print axioms EndgameChess.Rules.KRKCastleSix.corner_prison
#check @EndgameChess.Rules.KRKCastleSix.cover_flip
#print axioms EndgameChess.Rules.KRKCastleSix.cover_flip
#check @EndgameChess.Rules.KRKCastleSix.home_prison
#print axioms EndgameChess.Rules.KRKCastleSix.home_prison
#check @EndgameChess.Rules.KRKCastleSix.castle_not_six
#print axioms EndgameChess.Rules.KRKCastleSix.castle_not_six
#check @EndgameChess.Rules.KRKCastleSix.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKCastleSix.winning_entry_not_castle
#check @EndgameChess.Rules.KRKCastleTen.inner_boundary_impossible
#print axioms EndgameChess.Rules.KRKCastleTen.inner_boundary_impossible
#check @EndgameChess.Rules.KRKCastleTen.bottom_interior_impossible
#print axioms EndgameChess.Rules.KRKCastleTen.bottom_interior_impossible
#check @EndgameChess.Rules.KRKCastleTen.nine_interior_impossible
#print axioms EndgameChess.Rules.KRKCastleTen.nine_interior_impossible
#check @EndgameChess.Rules.KRKCastleTen.interior_covered
#print axioms EndgameChess.Rules.KRKCastleTen.interior_covered
#check @EndgameChess.Rules.KRKCastleTen.king_bottom_no_ten
#print axioms EndgameChess.Rules.KRKCastleTen.king_bottom_no_ten
#check @EndgameChess.Rules.KRKCastleTen.queen_bottom_weak_corner
#print axioms EndgameChess.Rules.KRKCastleTen.queen_bottom_weak_corner
#check @EndgameChess.Rules.KRKCastleTen.home_king_no_ten
#print axioms EndgameChess.Rules.KRKCastleTen.home_king_no_ten
#check @EndgameChess.Rules.KRKCastleTen.home_queen_weak_corner
#print axioms EndgameChess.Rules.KRKCastleTen.home_queen_weak_corner
#check @EndgameChess.Rules.KRKCastleTen.castle_not_ten
#print axioms EndgameChess.Rules.KRKCastleTen.castle_not_ten
#check @EndgameChess.Rules.KRKCastleTen.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKCastleTen.winning_entry_not_castle
#check @EndgameChess.Rules.KRKCastleTwelve.eleven_interior_impossible
#print axioms EndgameChess.Rules.KRKCastleTwelve.eleven_interior_impossible
#check @EndgameChess.Rules.KRKCastleTwelve.interior_covered
#print axioms EndgameChess.Rules.KRKCastleTwelve.interior_covered
#check @EndgameChess.Rules.KRKCastleTwelve.king_bottom_no_twelve
#print axioms EndgameChess.Rules.KRKCastleTwelve.king_bottom_no_twelve
#check @EndgameChess.Rules.KRKCastleTwelve.queen_bottom_weak_corner
#print axioms EndgameChess.Rules.KRKCastleTwelve.queen_bottom_weak_corner
#check @EndgameChess.Rules.KRKCastleTwelve.home_king_no_twelve
#print axioms EndgameChess.Rules.KRKCastleTwelve.home_king_no_twelve
#check @EndgameChess.Rules.KRKCastleTwelve.home_queen_weak_corner
#print axioms EndgameChess.Rules.KRKCastleTwelve.home_queen_weak_corner
#check @EndgameChess.Rules.KRKCastleTwelve.castle_not_twelve
#print axioms EndgameChess.Rules.KRKCastleTwelve.castle_not_twelve
#check @EndgameChess.Rules.KRKCastleTwelve.winning_entry_not_castle
#print axioms EndgameChess.Rules.KRKCastleTwelve.winning_entry_not_castle
#check @EndgameChess.Rules.KRKCentralWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_force_iff
#check @EndgameChess.Rules.KRKCentralWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_actual_iff
#check @EndgameChess.Rules.KRKCentralWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_hold_iff
#check @EndgameChess.Rules.KRKCentralWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_draw_iff
#check @EndgameChess.Rules.KRKCentralWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKCentralWeakBand.high_clock_distance_cases
#check @EndgameChess.Rules.KRKCornerSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_geometry
#check @EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_distance
#check @EndgameChess.Rules.KRKCornerSlotBarriers.slot_far
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_far
#check @EndgameChess.Rules.KRKCornerSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.last_slots_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.slot_not_rook
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_not_rook
#check @EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_legal
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.slot_reply_legal
#check @EndgameChess.Rules.KRKCornerSlotBarriers.ray_sees_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.ray_sees_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.line_target
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.line_target
#check @EndgameChess.Rules.KRKCornerSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.king_history_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.rook_history_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_force_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_actual_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_hold_iff
#check @EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKCornerSlotBarriers.high_clock_distance_cases
#check @EndgameChess.Rules.KRKSlotPrefix.Corner.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Corner.clear_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Corner.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Corner.history_append_iff
#check @EndgameChess.Rules.KRKCornerWeakBand.guard_legal
#print axioms EndgameChess.Rules.KRKCornerWeakBand.guard_legal
#check @EndgameChess.Rules.KRKCornerWeakBand.step_guard
#print axioms EndgameChess.Rules.KRKCornerWeakBand.step_guard
#check @EndgameChess.Rules.KRKCornerWeakBand.neighbour_cases
#print axioms EndgameChess.Rules.KRKCornerWeakBand.neighbour_cases
#check @EndgameChess.Rules.KRKCornerWeakBand.necessary
#print axioms EndgameChess.Rules.KRKCornerWeakBand.necessary
#check @EndgameChess.Rules.KRKCornerWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKCornerWeakBand.sufficient
#check @EndgameChess.Rules.KRKCornerWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_force_iff
#check @EndgameChess.Rules.KRKCornerWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_actual_iff
#check @EndgameChess.Rules.KRKCornerWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_hold_iff
#check @EndgameChess.Rules.KRKCornerWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_draw_iff
#check @EndgameChess.Rules.KRKCornerWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKCornerWeakBand.high_clock_distance_cases
#check @EndgameChess.Rules.KRKDeadline.winning_deadline
#print axioms EndgameChess.Rules.KRKDeadline.winning_deadline
#check @EndgameChess.Rules.KRKDistanceParity.weak_one_goal
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_one_goal
#check @EndgameChess.Rules.KRKDistanceParity.strong_two_one
#print axioms EndgameChess.Rules.KRKDistanceParity.strong_two_one
#check @EndgameChess.Rules.KRKDistanceParity.weak_three_two
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_three_two
#check @EndgameChess.Rules.KRKDistanceParity.strong_four_three
#print axioms EndgameChess.Rules.KRKDistanceParity.strong_four_three
#check @EndgameChess.Rules.KRKDistanceParity.weak_five_four
#print axioms EndgameChess.Rules.KRKDistanceParity.weak_five_four
#check @EndgameChess.Rules.KRKEdgeDepth.depth_step
#print axioms EndgameChess.Rules.KRKEdgeDepth.depth_step
#check @EndgameChess.Rules.KRKEdgeDepth.terminal_depth_zero
#print axioms EndgameChess.Rules.KRKEdgeDepth.terminal_depth_zero
#check @EndgameChess.Rules.KRKEdgeDepth.horizontal_predecessor
#print axioms EndgameChess.Rules.KRKEdgeDepth.horizontal_predecessor
#check @EndgameChess.Rules.KRKEdgeDepth.ready_predecessor_depth_zero
#print axioms EndgameChess.Rules.KRKEdgeDepth.ready_predecessor_depth_zero
#check @EndgameChess.Rules.KRKEdgeDepth.weak_interior_not_three
#print axioms EndgameChess.Rules.KRKEdgeDepth.weak_interior_not_three
#check @EndgameChess.Rules.KRKEdgeDepth.arrival_far
#print axioms EndgameChess.Rules.KRKEdgeDepth.arrival_far
#check @EndgameChess.Rules.KRKEdgeDepth.mate_depth_lower
#print axioms EndgameChess.Rules.KRKEdgeDepth.mate_depth_lower
#check @EndgameChess.Rules.KRKEdgeDepth.clock_depth_necessary
#print axioms EndgameChess.Rules.KRKEdgeDepth.clock_depth_necessary
#check @EndgameChess.Rules.KRKEdgeDepth.clock_depth_holding
#print axioms EndgameChess.Rules.KRKEdgeDepth.clock_depth_holding
#check @EndgameChess.Rules.KRKEightCentralStrip.prison
#print axioms EndgameChess.Rules.KRKEightCentralStrip.prison
#check @EndgameChess.Rules.KRKEightCentralStrip.not_clear
#print axioms EndgameChess.Rules.KRKEightCentralStrip.not_clear
#check @EndgameChess.Rules.KRKEightCentralStrip.kernel_no_eight
#print axioms EndgameChess.Rules.KRKEightCentralStrip.kernel_no_eight
#check @EndgameChess.Rules.KRKEightCentralStrip.middle_not_clear
#print axioms EndgameChess.Rules.KRKEightCentralStrip.middle_not_clear
#check @EndgameChess.Rules.KRKEightCentralStrip.middle_kernel_no_eight
#print axioms EndgameChess.Rules.KRKEightCentralStrip.middle_kernel_no_eight
#check @EndgameChess.Rules.KRKEightCentralStripHolding.strong_no_ten
#print axioms EndgameChess.Rules.KRKEightCentralStripHolding.strong_no_ten
#check @EndgameChess.Rules.KRKEightCentralStripHolding.high_clock_holding
#print axioms EndgameChess.Rules.KRKEightCentralStripHolding.high_clock_holding
#check @EndgameChess.Rules.KRKEightDiagonalEntries.corner_clear
#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.corner_clear
#check @EndgameChess.Rules.KRKEightDiagonalEntries.corner_region
#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.corner_region
#check @EndgameChess.Rules.KRKEightDiagonalEntries.near_region
#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.near_region
#check @EndgameChess.Rules.KRKEightDiagonalEntries.second_region
#print axioms EndgameChess.Rules.KRKEightDiagonalEntries.second_region
#check @EndgameChess.Rules.KRKEightEdge.seven_test_iff
#print axioms EndgameChess.Rules.KRKEightEdge.seven_test_iff
#check @EndgameChess.Rules.KRKEightEdge.reply_point
#print axioms EndgameChess.Rules.KRKEightEdge.reply_point
#check @EndgameChess.Rules.KRKEightEdge.clear_iff
#print axioms EndgameChess.Rules.KRKEightEdge.clear_iff
#check @EndgameChess.Rules.KRKEightEdge.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightEdge.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightGeometry.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightGeometry.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightGeometry.strong_eight_seven
#print axioms EndgameChess.Rules.KRKEightGeometry.strong_eight_seven
#check @EndgameChess.Rules.KRKEightGeometry.weak_nine_eight
#print axioms EndgameChess.Rules.KRKEightGeometry.weak_nine_eight
#check @EndgameChess.Rules.KRKEightGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.edge_clear_iff
#check @EndgameChess.Rules.KRKEightGlobal.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightGlobal.region_live
#print axioms EndgameChess.Rules.KRKEightGlobal.region_live
#check @EndgameChess.Rules.KRKEightGlobal.kernel_exact_eight_iff
#print axioms EndgameChess.Rules.KRKEightGlobal.kernel_exact_eight_iff
#check @EndgameChess.Rules.KRKEightInner.prison
#print axioms EndgameChess.Rules.KRKEightInner.prison
#check @EndgameChess.Rules.KRKEightInner.row_two_necessary
#print axioms EndgameChess.Rules.KRKEightInner.row_two_necessary
#check @EndgameChess.Rules.KRKEightInner.file_one_necessary
#print axioms EndgameChess.Rules.KRKEightInner.file_one_necessary
#check @EndgameChess.Rules.KRKEightInner.no_seven_diagonal
#print axioms EndgameChess.Rules.KRKEightInner.no_seven_diagonal
#check @EndgameChess.Rules.KRKEightInner.diagonal_not_clear
#print axioms EndgameChess.Rules.KRKEightInner.diagonal_not_clear
#check @EndgameChess.Rules.KRKEightInner.necessary
#print axioms EndgameChess.Rules.KRKEightInner.necessary
#check @EndgameChess.Rules.KRKEightInner.horizontal_replies
#print axioms EndgameChess.Rules.KRKEightInner.horizontal_replies
#check @EndgameChess.Rules.KRKEightInner.horizontal_clear
#print axioms EndgameChess.Rules.KRKEightInner.horizontal_clear
#check @EndgameChess.Rules.KRKEightInner.sufficient
#print axioms EndgameChess.Rules.KRKEightInner.sufficient
#check @EndgameChess.Rules.KRKEightInner.clear_iff
#print axioms EndgameChess.Rules.KRKEightInner.clear_iff
#check @EndgameChess.Rules.KRKEightInner.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightInner.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightInner.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKEightInner.kernel_exact_eight
#check @EndgameChess.Rules.KRKEightInner.framed_clear_iff
#print axioms EndgameChess.Rules.KRKEightInner.framed_clear_iff
#check @EndgameChess.Rules.KRKEightInterior.covered_or_inner
#print axioms EndgameChess.Rules.KRKEightInterior.covered_or_inner
#check @EndgameChess.Rules.KRKEightInterior.deep_escape
#print axioms EndgameChess.Rules.KRKEightInterior.deep_escape
#check @EndgameChess.Rules.KRKEightInterior.weak_eight_depth_le_one
#print axioms EndgameChess.Rules.KRKEightInterior.weak_eight_depth_le_one
#check @EndgameChess.Rules.KRKEightInteriorExact.strip_spec
#print axioms EndgameChess.Rules.KRKEightInteriorExact.strip_spec
#check @EndgameChess.Rules.KRKEightInteriorExact.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightInteriorExact.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightInteriorExact.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKEightInteriorExact.kernel_exact_eight
#check @EndgameChess.Rules.KRKEightInteriorHolding.strong_ten_depth_le_one
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.strong_ten_depth_le_one
#check @EndgameChess.Rules.KRKEightInteriorHolding.high_clock_depth_necessary
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.high_clock_depth_necessary
#check @EndgameChess.Rules.KRKEightInteriorHolding.high_clock_deep_holding
#print axioms EndgameChess.Rules.KRKEightInteriorHolding.high_clock_deep_holding
#check @EndgameChess.Rules.KRKEightNearStrip.prison
#print axioms EndgameChess.Rules.KRKEightNearStrip.prison
#check @EndgameChess.Rules.KRKEightNearStrip.no_upper_king
#print axioms EndgameChess.Rules.KRKEightNearStrip.no_upper_king
#check @EndgameChess.Rules.KRKEightNearStrip.file_one_requires_row_three
#print axioms EndgameChess.Rules.KRKEightNearStrip.file_one_requires_row_three
#check @EndgameChess.Rules.KRKEightNearStrip.row_three_necessary
#print axioms EndgameChess.Rules.KRKEightNearStrip.row_three_necessary
#check @EndgameChess.Rules.KRKEightNearStrip.necessary
#print axioms EndgameChess.Rules.KRKEightNearStrip.necessary
#check @EndgameChess.Rules.KRKEightNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKEightNearStrip.clear_iff
#check @EndgameChess.Rules.KRKEightNearStrip.kernel_eight_iff
#print axioms EndgameChess.Rules.KRKEightNearStrip.kernel_eight_iff
#check @EndgameChess.Rules.KRKEightNearStrip.framed_clear_iff
#print axioms EndgameChess.Rules.KRKEightNearStrip.framed_clear_iff
#check @EndgameChess.Rules.KRKEightPlyExact.necessary
#print axioms EndgameChess.Rules.KRKEightPlyExact.necessary
#check @EndgameChess.Rules.KRKEightPlyExact.rule_eight_iff
#print axioms EndgameChess.Rules.KRKEightPlyExact.rule_eight_iff
#check @EndgameChess.Rules.KRKEightPlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKEightPlyExact.distance_cases
#check @EndgameChess.Rules.KRKEightPlyHistory.child_seven_certificate
#print axioms EndgameChess.Rules.KRKEightPlyHistory.child_seven_certificate
#check @EndgameChess.Rules.KRKEightPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKEightPlyHistory.necessary
#check @EndgameChess.Rules.KRKEightPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKEightPlyHistory.sufficient
#check @EndgameChess.Rules.KRKEightPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKEightPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKEightPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKEightPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKEightPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKEightPlyHistory.high_clock_distance_cases
#check @EndgameChess.Rules.KRKEightPrefix.prefix_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.prefix_occurrences_eq
#check @EndgameChess.Rules.KRKEightPrefix.root_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.root_occurrences_eq
#check @EndgameChess.Rules.KRKEightPrefix.first_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.first_occurrences_eq
#check @EndgameChess.Rules.KRKEightPrefix.second_occurrences_eq
#print axioms EndgameChess.Rules.KRKEightPrefix.second_occurrences_eq
#check @EndgameChess.Rules.KRKEightPrefix.fourth_entry_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.fourth_entry_weak_iff
#check @EndgameChess.Rules.KRKEightPrefix.inner_clear_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.inner_clear_weak_iff
#check @EndgameChess.Rules.KRKEightPrefix.weak_after_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.weak_after_weak_iff
#check @EndgameChess.Rules.KRKEightPrefix.strong_clear_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.strong_clear_weak_iff
#check @EndgameChess.Rules.KRKEightPrefix.six_after_weak_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.six_after_weak_iff
#check @EndgameChess.Rules.KRKEightPrefix.seven_append_iff
#print axioms EndgameChess.Rules.KRKEightPrefix.seven_append_iff
#check @EndgameChess.Rules.KRKEightStrip.region_replies
#print axioms EndgameChess.Rules.KRKEightStrip.region_replies
#check @EndgameChess.Rules.KRKEightStrip.region_clear
#print axioms EndgameChess.Rules.KRKEightStrip.region_clear
#check @EndgameChess.Rules.KRKEightStrip.kernel_exact_eight
#print axioms EndgameChess.Rules.KRKEightStrip.kernel_exact_eight
#check @EndgameChess.Rules.KRKElevenEdge.clear_iff
#print axioms EndgameChess.Rules.KRKElevenEdge.clear_iff
#check @EndgameChess.Rules.KRKElevenEdge.kernel_eleven_iff
#print axioms EndgameChess.Rules.KRKElevenEdge.kernel_eleven_iff
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.inner_file_bound
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.inner_file_bound
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.near_rank_bound
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_rank_bound
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_eight
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_eight
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_upper_low_rook
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_upper_low_rook
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_nine
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_two_not_nine
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.ten_high_near_cover
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.ten_high_near_cover
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_ten_high_rook_rank
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_ten_high_rook_rank
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_two_not_eleven
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_two_not_eleven
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_one_not_eleven
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_one_not_eleven
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_eight
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_eight
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_nine
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_five_zero_not_nine
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_ten_high_rook_rank
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_ten_high_rook_rank
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_zero_not_eleven
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_five_zero_not_eleven
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.near_ten_high_rook_rank
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_ten_high_rook_rank
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.near_five_one_not_eleven
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.near_five_one_not_eleven
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_low_row_not_eight
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_low_row_not_eight
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_not_eight
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_not_eight
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_eight
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_eight
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_nine
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_left_high_rook_not_nine
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_low_row_not_nine
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.middle_one_three_low_row_not_nine
#check @EndgameChess.Rules.KRKElevenEdgeBoundary.second_one_three_high_rook_not_eleven
#print axioms EndgameChess.Rules.KRKElevenEdgeBoundary.second_one_three_high_rook_not_eleven
#check @EndgameChess.Rules.KRKElevenEntry.ten_entry_move
#print axioms EndgameChess.Rules.KRKElevenEntry.ten_entry_move
#check @EndgameChess.Rules.KRKElevenGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKElevenGeometry.entry_sufficient
#check @EndgameChess.Rules.KRKElevenGeometry.sufficient
#print axioms EndgameChess.Rules.KRKElevenGeometry.sufficient
#check @EndgameChess.Rules.KRKElevenGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKElevenGeometry.entry_necessary
#check @EndgameChess.Rules.KRKElevenGeometry.necessary
#print axioms EndgameChess.Rules.KRKElevenGeometry.necessary
#check @EndgameChess.Rules.KRKElevenGeometry.kernel_eleven_iff
#print axioms EndgameChess.Rules.KRKElevenGeometry.kernel_eleven_iff
#check @EndgameChess.Rules.KRKElevenGeometry.frame_map
#print axioms EndgameChess.Rules.KRKElevenGeometry.frame_map
#check @EndgameChess.Rules.KRKElevenGeometry.king_step_clear
#print axioms EndgameChess.Rules.KRKElevenGeometry.king_step_clear
#check @EndgameChess.Rules.KRKElevenGeometry.rook_step_clear
#print axioms EndgameChess.Rules.KRKElevenGeometry.rook_step_clear
#check @EndgameChess.Rules.KRKElevenInner.horizontal_shape
#print axioms EndgameChess.Rules.KRKElevenInner.horizontal_shape
#check @EndgameChess.Rules.KRKElevenInner.global_region_iff
#print axioms EndgameChess.Rules.KRKElevenInner.global_region_iff
#check @EndgameChess.Rules.KRKElevenInner.king_points_iff
#print axioms EndgameChess.Rules.KRKElevenInner.king_points_iff
#check @EndgameChess.Rules.KRKElevenInner.rook_line_necessary
#print axioms EndgameChess.Rules.KRKElevenInner.rook_line_necessary
#check @EndgameChess.Rules.KRKElevenInner.rook_destination
#print axioms EndgameChess.Rules.KRKElevenInner.rook_destination
#check @EndgameChess.Rules.KRKElevenInner.rook_rays_necessary
#print axioms EndgameChess.Rules.KRKElevenInner.rook_rays_necessary
#check @EndgameChess.Rules.KRKElevenInner.canonical_rook_clear
#print axioms EndgameChess.Rules.KRKElevenInner.canonical_rook_clear
#check @EndgameChess.Rules.KRKElevenInner.clear_iff
#print axioms EndgameChess.Rules.KRKElevenInner.clear_iff
#check @EndgameChess.Rules.KRKElevenInner.kernel_eleven_iff
#print axioms EndgameChess.Rules.KRKElevenInner.kernel_eleven_iff
#check @EndgameChess.Rules.KRKElevenInner.kernel_exact_eleven
#print axioms EndgameChess.Rules.KRKElevenInner.kernel_exact_eleven
#check @EndgameChess.Rules.KRKElevenInner.framed_clear_iff
#print axioms EndgameChess.Rules.KRKElevenInner.framed_clear_iff
#check @EndgameChess.Rules.KRKElevenNearBoundary.upper_necessary
#print axioms EndgameChess.Rules.KRKElevenNearBoundary.upper_necessary
#check @EndgameChess.Rules.KRKElevenNearBoundary.two_four_not_clear
#print axioms EndgameChess.Rules.KRKElevenNearBoundary.two_four_not_clear
#check @EndgameChess.Rules.KRKElevenNearBoundary.upper_sufficient
#print axioms EndgameChess.Rules.KRKElevenNearBoundary.upper_sufficient
#check @EndgameChess.Rules.KRKElevenNearStrip.region_shape
#print axioms EndgameChess.Rules.KRKElevenNearStrip.region_shape
#check @EndgameChess.Rules.KRKElevenNearStrip.global_region_iff
#print axioms EndgameChess.Rules.KRKElevenNearStrip.global_region_iff
#check @EndgameChess.Rules.KRKElevenNearStrip.rook_line_necessary
#print axioms EndgameChess.Rules.KRKElevenNearStrip.rook_line_necessary
#check @EndgameChess.Rules.KRKElevenNearStrip.rook_destination
#print axioms EndgameChess.Rules.KRKElevenNearStrip.rook_destination
#check @EndgameChess.Rules.KRKElevenNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKElevenNearStrip.clear_iff
#check @EndgameChess.Rules.KRKElevenNearStrip.kernel_eleven_iff
#print axioms EndgameChess.Rules.KRKElevenNearStrip.kernel_eleven_iff
#check @EndgameChess.Rules.KRKElevenNearStrip.kernel_exact_eleven
#print axioms EndgameChess.Rules.KRKElevenNearStrip.kernel_exact_eleven
#check @EndgameChess.Rules.KRKElevenNearStrip.framed_clear_iff
#print axioms EndgameChess.Rules.KRKElevenNearStrip.framed_clear_iff
#check @EndgameChess.Rules.KRKElevenPlyExact.necessary
#print axioms EndgameChess.Rules.KRKElevenPlyExact.necessary
#check @EndgameChess.Rules.KRKElevenPlyExact.rule_eleven_iff
#print axioms EndgameChess.Rules.KRKElevenPlyExact.rule_eleven_iff
#check @EndgameChess.Rules.KRKElevenPlyExact.strong_twelve_eleven
#print axioms EndgameChess.Rules.KRKElevenPlyExact.strong_twelve_eleven
#check @EndgameChess.Rules.KRKElevenPlyExact.weak_thirteen_twelve
#print axioms EndgameChess.Rules.KRKElevenPlyExact.weak_thirteen_twelve
#check @EndgameChess.Rules.KRKElevenPlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKElevenPlyExact.distance_cases
#check @EndgameChess.Rules.KRKElevenPlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKElevenPlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKElevenPlyHistory.clear_geometry
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.clear_geometry
#check @EndgameChess.Rules.KRKElevenPlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.clear_kernel
#check @EndgameChess.Rules.KRKElevenPlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.entry_certificate
#check @EndgameChess.Rules.KRKElevenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.sufficient
#check @EndgameChess.Rules.KRKElevenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.necessary
#check @EndgameChess.Rules.KRKElevenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKElevenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKElevenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKElevenPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKElevenSlots.nine_test_rank
#print axioms EndgameChess.Rules.KRKElevenSlots.nine_test_rank
#check @EndgameChess.Rules.KRKElevenSlots.region_rank
#print axioms EndgameChess.Rules.KRKElevenSlots.region_rank
#check @EndgameChess.Rules.KRKElevenSlots.region_point
#print axioms EndgameChess.Rules.KRKElevenSlots.region_point
#check @EndgameChess.Rules.KRKFiveCornerEntries.slot22_properties
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.slot22_properties
#check @EndgameChess.Rules.KRKFiveCornerEntries.corner22_reachable
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_reachable
#check @EndgameChess.Rules.KRKFiveCornerEntries.corner22_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_five
#check @EndgameChess.Rules.KRKFiveCornerEntries.corner22_king_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.corner22_king_five
#check @EndgameChess.Rules.KRKFiveCornerEntries.low_right_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.low_right_five
#check @EndgameChess.Rules.KRKFiveCornerEntries.side_right_five
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.side_right_five
#check @EndgameChess.Rules.KRKFiveCornerEntries.no_capture_square_entry
#print axioms EndgameChess.Rules.KRKFiveCornerEntries.no_capture_square_entry
#check @EndgameChess.Rules.KRKFiveGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKFiveGeometry.entry_sufficient
#check @EndgameChess.Rules.KRKFiveGeometry.sufficient
#print axioms EndgameChess.Rules.KRKFiveGeometry.sufficient
#check @EndgameChess.Rules.KRKFiveGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKFiveGeometry.entry_necessary
#check @EndgameChess.Rules.KRKFiveGeometry.necessary
#print axioms EndgameChess.Rules.KRKFiveGeometry.necessary
#check @EndgameChess.Rules.KRKFiveGeometry.kernel_five_iff
#print axioms EndgameChess.Rules.KRKFiveGeometry.kernel_five_iff
#check @EndgameChess.Rules.KRKFiveGeometry.map
#print axioms EndgameChess.Rules.KRKFiveGeometry.map
#check @EndgameChess.Rules.KRKFiveGeometry.map_iff
#print axioms EndgameChess.Rules.KRKFiveGeometry.map_iff
#check @EndgameChess.Rules.KRKFiveMiddle.normalize_f
#print axioms EndgameChess.Rules.KRKFiveMiddle.normalize_f
#check @EndgameChess.Rules.KRKFiveMiddle.normalize_r
#print axioms EndgameChess.Rules.KRKFiveMiddle.normalize_r
#check @EndgameChess.Rules.KRKFiveMiddle.middle_slot_properties
#print axioms EndgameChess.Rules.KRKFiveMiddle.middle_slot_properties
#check @EndgameChess.Rules.KRKFiveMiddle.king_points_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.king_points_iff
#check @EndgameChess.Rules.KRKFiveMiddle.middle_reachable
#print axioms EndgameChess.Rules.KRKFiveMiddle.middle_reachable
#check @EndgameChess.Rules.KRKFiveMiddle.west_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.west_reachable_iff
#check @EndgameChess.Rules.KRKFiveMiddle.east_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.east_reachable_iff
#check @EndgameChess.Rules.KRKFiveMiddle.rook_rays_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.rook_rays_iff
#check @EndgameChess.Rules.KRKFiveMiddle.clear_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.clear_iff
#check @EndgameChess.Rules.KRKFiveMiddle.kernel_five_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.kernel_five_iff
#check @EndgameChess.Rules.KRKFiveMiddle.bottom_clear_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.bottom_clear_iff
#check @EndgameChess.Rules.KRKFiveMiddle.low_rook_bottom_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.low_rook_bottom_iff
#check @EndgameChess.Rules.KRKFiveMiddle.rank_two_bottom_iff
#print axioms EndgameChess.Rules.KRKFiveMiddle.rank_two_bottom_iff
#check @EndgameChess.Rules.KRKFiveNear.near_slot_properties
#print axioms EndgameChess.Rules.KRKFiveNear.near_slot_properties
#check @EndgameChess.Rules.KRKFiveNear.king_points_iff
#print axioms EndgameChess.Rules.KRKFiveNear.king_points_iff
#check @EndgameChess.Rules.KRKFiveNear.west_reachable_iff
#print axioms EndgameChess.Rules.KRKFiveNear.west_reachable_iff
#check @EndgameChess.Rules.KRKFiveNear.middle_reachable
#print axioms EndgameChess.Rules.KRKFiveNear.middle_reachable
#check @EndgameChess.Rules.KRKFiveNear.east_reachable
#print axioms EndgameChess.Rules.KRKFiveNear.east_reachable
#check @EndgameChess.Rules.KRKFiveNear.rook_rays_iff
#print axioms EndgameChess.Rules.KRKFiveNear.rook_rays_iff
#check @EndgameChess.Rules.KRKFiveNear.clear_iff
#print axioms EndgameChess.Rules.KRKFiveNear.clear_iff
#check @EndgameChess.Rules.KRKFiveNear.kernel_five_iff
#print axioms EndgameChess.Rules.KRKFiveNear.kernel_five_iff
#check @EndgameChess.Rules.KRKFivePlyExact.necessary
#print axioms EndgameChess.Rules.KRKFivePlyExact.necessary
#check @EndgameChess.Rules.KRKFivePlyExact.rule_five_iff
#print axioms EndgameChess.Rules.KRKFivePlyExact.rule_five_iff
#check @EndgameChess.Rules.KRKFivePlyExact.strong_six_five
#print axioms EndgameChess.Rules.KRKFivePlyExact.strong_six_five
#check @EndgameChess.Rules.KRKFivePlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKFivePlyHistory.entry_certificate
#check @EndgameChess.Rules.KRKFivePlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKFivePlyHistory.sufficient
#check @EndgameChess.Rules.KRKFivePlyHistory.entry_kernel
#print axioms EndgameChess.Rules.KRKFivePlyHistory.entry_kernel
#check @EndgameChess.Rules.KRKFivePlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKFivePlyHistory.clear_kernel
#check @EndgameChess.Rules.KRKFivePlyHistory.necessary
#print axioms EndgameChess.Rules.KRKFivePlyHistory.necessary
#check @EndgameChess.Rules.KRKFivePlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKFivePlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKFivePlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKFivePlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKFivePlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKFivePlyHistory.high_clock_distance_cases
#check @EndgameChess.Rules.KRKFiveWeakPrefix.first_occurrences_eq
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.first_occurrences_eq
#check @EndgameChess.Rules.KRKFiveWeakPrefix.second_occurrences_eq
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.second_occurrences_eq
#check @EndgameChess.Rules.KRKFiveWeakPrefix.fourth_entry_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.fourth_entry_append_iff
#check @EndgameChess.Rules.KRKFiveWeakPrefix.inner_clear_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.inner_clear_append_iff
#check @EndgameChess.Rules.KRKFiveWeakPrefix.weak_after_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.weak_after_append_iff
#check @EndgameChess.Rules.KRKFiveWeakPrefix.strong_clear_append_iff
#print axioms EndgameChess.Rules.KRKFiveWeakPrefix.strong_clear_append_iff
#check @EndgameChess.Rules.KRKFourGeometry.three_map
#print axioms EndgameChess.Rules.KRKFourGeometry.three_map
#check @EndgameChess.Rules.KRKFourGeometry.three_iff
#print axioms EndgameChess.Rules.KRKFourGeometry.three_iff
#check @EndgameChess.Rules.KRKFourGeometry.framed_shape_necessary
#print axioms EndgameChess.Rules.KRKFourGeometry.framed_shape_necessary
#check @EndgameChess.Rules.KRKFourGeometry.global_shape_necessary
#print axioms EndgameChess.Rules.KRKFourGeometry.global_shape_necessary
#check @EndgameChess.Rules.KRKFourGeometry.framed_shape_sufficient
#print axioms EndgameChess.Rules.KRKFourGeometry.framed_shape_sufficient
#check @EndgameChess.Rules.KRKFourGeometry.global_shape_sufficient
#print axioms EndgameChess.Rules.KRKFourGeometry.global_shape_sufficient
#check @EndgameChess.Rules.KRKFourPlyCorner.corner_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_necessary
#check @EndgameChess.Rules.KRKFourPlyCorner.corner_four_replies
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_replies
#check @EndgameChess.Rules.KRKFourPlyCorner.corner_four_safe
#print axioms EndgameChess.Rules.KRKFourPlyCorner.corner_four_safe
#check @EndgameChess.Rules.KRKFourPlyCorner.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyCorner.weak_four_iff
#check @EndgameChess.Rules.KRKFourPlyEscape.last_depth_zero
#print axioms EndgameChess.Rules.KRKFourPlyEscape.last_depth_zero
#check @EndgameChess.Rules.KRKFourPlyEscape.three_depth_zero
#print axioms EndgameChess.Rules.KRKFourPlyEscape.three_depth_zero
#check @EndgameChess.Rules.KRKFourPlyEscape.interior_neighbour_covered
#print axioms EndgameChess.Rules.KRKFourPlyEscape.interior_neighbour_covered
#check @EndgameChess.Rules.KRKFourPlyEscape.covered_box
#print axioms EndgameChess.Rules.KRKFourPlyEscape.covered_box
#check @EndgameChess.Rules.KRKFourPlyEscape.strip_prison
#print axioms EndgameChess.Rules.KRKFourPlyEscape.strip_prison
#check @EndgameChess.Rules.KRKFourPlyEscape.corner_prison
#print axioms EndgameChess.Rules.KRKFourPlyEscape.corner_prison
#check @EndgameChess.Rules.KRKFourPlyEscape.corner_escape
#print axioms EndgameChess.Rules.KRKFourPlyEscape.corner_escape
#check @EndgameChess.Rules.KRKFourPlyEscape.strip_escape
#print axioms EndgameChess.Rules.KRKFourPlyEscape.strip_escape
#check @EndgameChess.Rules.KRKFourPlyExact.necessary
#print axioms EndgameChess.Rules.KRKFourPlyExact.necessary
#check @EndgameChess.Rules.KRKFourPlyExact.rule_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyExact.rule_four_iff
#check @EndgameChess.Rules.KRKFourPlyEscape.three_map
#print axioms EndgameChess.Rules.KRKFourPlyEscape.three_map
#check @EndgameChess.Rules.KRKFourPlyEscape.deep_prison_impossible
#print axioms EndgameChess.Rules.KRKFourPlyEscape.deep_prison_impossible
#check @EndgameChess.Rules.KRKFourPlyEscape.interior_four_impossible
#print axioms EndgameChess.Rules.KRKFourPlyEscape.interior_four_impossible
#check @EndgameChess.Rules.KRKFourPlyMiddle.covered_or_middle
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.covered_or_middle
#check @EndgameChess.Rules.KRKFourPlyMiddle.central_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.central_four_necessary
#check @EndgameChess.Rules.KRKFourPlyMiddle.opposition_replies
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.opposition_replies
#check @EndgameChess.Rules.KRKFourPlyMiddle.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyMiddle.weak_four_iff
#check @EndgameChess.Rules.KRKFourPlyNearCorner.covered_or_swapped_near
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.covered_or_swapped_near
#check @EndgameChess.Rules.KRKFourPlyNearCorner.near_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_necessary
#check @EndgameChess.Rules.KRKFourPlyNearCorner.near_four_replies
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_replies
#check @EndgameChess.Rules.KRKFourPlyNearCorner.near_four_safe
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.near_four_safe
#check @EndgameChess.Rules.KRKFourPlyNearCorner.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlyNearCorner.weak_four_iff
#check @EndgameChess.Rules.KRKFourPlySecond.covered_or_near
#print axioms EndgameChess.Rules.KRKFourPlySecond.covered_or_near
#check @EndgameChess.Rules.KRKFourPlySecond.second_four_necessary
#print axioms EndgameChess.Rules.KRKFourPlySecond.second_four_necessary
#check @EndgameChess.Rules.KRKFourPlySecond.opposition_replies
#print axioms EndgameChess.Rules.KRKFourPlySecond.opposition_replies
#check @EndgameChess.Rules.KRKFourPlySecond.weak_four_iff
#print axioms EndgameChess.Rules.KRKFourPlySecond.weak_four_iff
#check @EndgameChess.Rules.KRKFourSlots.shape_iff
#print axioms EndgameChess.Rules.KRKFourSlots.shape_iff
#check @EndgameChess.Rules.KRKFourSlots.entry_candidates
#print axioms EndgameChess.Rules.KRKFourSlots.entry_candidates
#check @EndgameChess.Rules.KRKFourSlots.high_clock_necessary
#print axioms EndgameChess.Rules.KRKFourSlots.high_clock_necessary
#check @EndgameChess.Rules.KRKFourteenCentralBounds.second_three_four_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.second_three_four_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.second_upper_row_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.second_upper_row_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.near_three_four_file_two_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_three_four_file_two_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.near_three_three_row_four_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_three_three_row_four_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_low_rook_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_low_rook_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_three_high_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.near_upper_three_high_no_thirteen
#check @EndgameChess.Rules.KRKFourteenCentralBounds.upper_two_above_no_clear
#print axioms EndgameChess.Rules.KRKFourteenCentralBounds.upper_two_above_no_clear
#check @EndgameChess.Rules.KRKFourteenCentralEntries.opposition_clear
#print axioms EndgameChess.Rules.KRKFourteenCentralEntries.opposition_clear
#check @EndgameChess.Rules.KRKFourteenCentralEntries.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenCentralEntries.kernel_exact_fourteen
#check @EndgameChess.Rules.KRKFourteenCentralExact.sufficient
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.sufficient
#check @EndgameChess.Rules.KRKFourteenCentralExact.clear_iff
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.clear_iff
#check @EndgameChess.Rules.KRKFourteenCentralExact.fresh_iff
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.fresh_iff
#check @EndgameChess.Rules.KRKFourteenCentralExact.kernel_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.kernel_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenCentralExact.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.kernel_exact_fourteen
#check @EndgameChess.Rules.KRKFourteenCentralExact.framed_clear_iff
#print axioms EndgameChess.Rules.KRKFourteenCentralExact.framed_clear_iff
#check @EndgameChess.Rules.KRKFourteenCentralNecessary.necessary
#print axioms EndgameChess.Rules.KRKFourteenCentralNecessary.necessary
#check @EndgameChess.Rules.KRKFourteenCentralPrison.legal_upper
#print axioms EndgameChess.Rules.KRKFourteenCentralPrison.legal_upper
#check @EndgameChess.Rules.KRKFourteenCentralPrison.prison
#print axioms EndgameChess.Rules.KRKFourteenCentralPrison.prison
#check @EndgameChess.Rules.KRKFourteenCentralUpperEntries.upper_one_clear
#print axioms EndgameChess.Rules.KRKFourteenCentralUpperEntries.upper_one_clear
#check @EndgameChess.Rules.KRKFourteenCentralUpperEntries.kernel_upper_one_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenCentralUpperEntries.kernel_upper_one_exact_fourteen
#check @EndgameChess.Rules.KRKFourteenCentralUpperTwo.clear
#print axioms EndgameChess.Rules.KRKFourteenCentralUpperTwo.clear
#check @EndgameChess.Rules.KRKFourteenCentralUpperZero.low_second_twelve
#print axioms EndgameChess.Rules.KRKFourteenCentralUpperZero.low_second_twelve
#check @EndgameChess.Rules.KRKFourteenCentralUpperZero.clear
#print axioms EndgameChess.Rules.KRKFourteenCentralUpperZero.clear
#check @EndgameChess.Rules.KRKFourteenDeep.bad_neighbour_covered
#print axioms EndgameChess.Rules.KRKFourteenDeep.bad_neighbour_covered
#check @EndgameChess.Rules.KRKFourteenDeep.central_three_no_clear
#print axioms EndgameChess.Rules.KRKFourteenDeep.central_three_no_clear
#check @EndgameChess.Rules.KRKFourteenDeep.central_no_clear
#print axioms EndgameChess.Rules.KRKFourteenDeep.central_no_clear
#check @EndgameChess.Rules.KRKFourteenDeep.kernel_central_no_fourteen
#print axioms EndgameChess.Rules.KRKFourteenDeep.kernel_central_no_fourteen
#check @EndgameChess.Rules.KRKFourteenDeepExact.fresh_iff
#print axioms EndgameChess.Rules.KRKFourteenDeepExact.fresh_iff
#check @EndgameChess.Rules.KRKFourteenDeepExact.kernel_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenDeepExact.kernel_exact_fourteen
#check @EndgameChess.Rules.KRKFourteenDeepStrip.prison
#print axioms EndgameChess.Rules.KRKFourteenDeepStrip.prison
#check @EndgameChess.Rules.KRKFourteenDeepStripHolding.near_corner_no_clear
#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.near_corner_no_clear
#check @EndgameChess.Rules.KRKFourteenDeepStripHolding.belt_no_clear
#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.belt_no_clear
#check @EndgameChess.Rules.KRKFourteenDeepStripHolding.deep_corner_necessary
#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.deep_corner_necessary
#check @EndgameChess.Rules.KRKFourteenDeepStripHolding.kernel_deep_corner_necessary
#print axioms EndgameChess.Rules.KRKFourteenDeepStripHolding.kernel_deep_corner_necessary
#check @EndgameChess.Rules.KRKFourteenGeometry.kernel_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenGeometry.kernel_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenGeometry.strong_fourteen_thirteen
#print axioms EndgameChess.Rules.KRKFourteenGeometry.strong_fourteen_thirteen
#check @EndgameChess.Rules.KRKFourteenGeometry.weak_fifteen_fourteen
#print axioms EndgameChess.Rules.KRKFourteenGeometry.weak_fifteen_fourteen
#check @EndgameChess.Rules.KRKFourteenGeometry.twelve_region_depth
#print axioms EndgameChess.Rules.KRKFourteenGeometry.twelve_region_depth
#check @EndgameChess.Rules.KRKFourteenGeometry.thirteen_weak_depth
#print axioms EndgameChess.Rules.KRKFourteenGeometry.thirteen_weak_depth
#check @EndgameChess.Rules.KRKFourteenGeometry.thirteen_deep_corner
#print axioms EndgameChess.Rules.KRKFourteenGeometry.thirteen_deep_corner
#check @EndgameChess.Rules.KRKFourteenGeometry.frame_map
#print axioms EndgameChess.Rules.KRKFourteenGeometry.frame_map
#check @EndgameChess.Rules.KRKFourteenPlyExact.necessary
#print axioms EndgameChess.Rules.KRKFourteenPlyExact.necessary
#check @EndgameChess.Rules.KRKFourteenPlyExact.rule_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyExact.rule_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenPlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKFourteenPlyExact.distance_cases
#check @EndgameChess.Rules.KRKFourteenPlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKFourteenPlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKFourteenPlyHistory.after_weak_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.after_weak_iff
#check @EndgameChess.Rules.KRKFourteenPlyHistory.child_thirteen_certificate
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.child_thirteen_certificate
#check @EndgameChess.Rules.KRKFourteenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.necessary
#check @EndgameChess.Rules.KRKFourteenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.sufficient
#check @EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKFourteenPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKFourteenSecondCorner.prison
#print axioms EndgameChess.Rules.KRKFourteenSecondCorner.prison
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_zero_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_zero_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_two_file_two_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_four_two_file_two_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_three_four_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.near_three_four_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_four_three_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_four_three_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_three_four_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.central_three_four_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerBounds.inner_diagonal_no_thirteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerBounds.inner_diagonal_no_thirteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerEntries.opposition_clear
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerEntries.opposition_clear
#check @EndgameChess.Rules.KRKFourteenSecondCornerEntries.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerEntries.kernel_exact_fourteen
#check @EndgameChess.Rules.KRKFourteenSecondCornerExact.necessary
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.necessary
#check @EndgameChess.Rules.KRKFourteenSecondCornerExact.sufficient
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.sufficient
#check @EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_fourteen_iff
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_fourteen_iff
#check @EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_exact_fourteen
#print axioms EndgameChess.Rules.KRKFourteenSecondCornerExact.kernel_exact_fourteen
#check @EndgameChess.Rules.KRKFrameBound.bound_transport
#print axioms EndgameChess.Rules.KRKFrameBound.bound_transport
#check @EndgameChess.Rules.KRKFrameBound.five_map
#print axioms EndgameChess.Rules.KRKFrameBound.five_map
#check @EndgameChess.Rules.KRKFrameBound.six_map
#print axioms EndgameChess.Rules.KRKFrameBound.six_map
#check @EndgameChess.Rules.KRKFramedHistory.ray_sees_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.ray_sees_iff
#check @EndgameChess.Rules.KRKFramedHistory.native_reply_step
#print axioms EndgameChess.Rules.KRKFramedHistory.native_reply_step
#check @EndgameChess.Rules.KRKFramedHistory.king_history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.king_history_iff
#check @EndgameChess.Rules.KRKFramedHistory.rook_history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.rook_history_iff
#check @EndgameChess.Rules.KRKFramedHistory.history_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.history_iff
#check @EndgameChess.Rules.KRKFramedHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKFramedHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKFramedHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKFramedHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_distance_cases
#check @EndgameChess.Rules.KRKFramedHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKFramedHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKFramedPrefix.point_append
#print axioms EndgameChess.Rules.KRKFramedPrefix.point_append
#check @EndgameChess.Rules.KRKFramedPrefix.ray_append
#print axioms EndgameChess.Rules.KRKFramedPrefix.ray_append
#check @EndgameChess.Rules.KRKFramedPrefix.clear_append_iff
#print axioms EndgameChess.Rules.KRKFramedPrefix.clear_append_iff
#check @EndgameChess.Rules.KRKFramedPrefix.history_append_iff
#print axioms EndgameChess.Rules.KRKFramedPrefix.history_append_iff
#check @EndgameChess.Rules.KRKGeometricSymmetry.last_valid
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_valid
#check @EndgameChess.Rules.KRKGeometricSymmetry.immediate_valid
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_valid
#check @EndgameChess.Rules.KRKGeometricSymmetry.last_map
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_map
#check @EndgameChess.Rules.KRKGeometricSymmetry.last_map_iff
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.last_map_iff
#check @EndgameChess.Rules.KRKGeometricSymmetry.immediate_map
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_map
#check @EndgameChess.Rules.KRKGeometricSymmetry.immediate_map_iff
#print axioms EndgameChess.Rules.KRKGeometricSymmetry.immediate_map_iff
#check @EndgameChess.Rules.KRKGlobalWeakBand.necessary
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.necessary
#check @EndgameChess.Rules.KRKGlobalWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.sufficient
#check @EndgameChess.Rules.KRKGlobalWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_force_iff
#check @EndgameChess.Rules.KRKGlobalWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_actual_iff
#check @EndgameChess.Rules.KRKGlobalWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_hold_iff
#check @EndgameChess.Rules.KRKGlobalWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_draw_iff
#check @EndgameChess.Rules.KRKGlobalWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKGlobalWeakBand.high_clock_distance_cases
#check @EndgameChess.Rules.KRKImmediate.immediate_iff
#print axioms EndgameChess.Rules.KRKImmediate.immediate_iff
#check @EndgameChess.Rules.KRKImmediate.admitted_immediate_iff
#print axioms EndgameChess.Rules.KRKImmediate.admitted_immediate_iff
#check @EndgameChess.Rules.KRKImmediate.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_force_iff
#check @EndgameChess.Rules.KRKImmediate.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_actual_iff
#check @EndgameChess.Rules.KRKImmediate.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKImmediate.high_clock_hold_iff
#check @EndgameChess.Rules.KRKFourPlyEscape.clock_depth_necessary
#print axioms EndgameChess.Rules.KRKFourPlyEscape.clock_depth_necessary
#check @EndgameChess.Rules.KRKFourPlyEscape.clock_depth_holding
#print axioms EndgameChess.Rules.KRKFourPlyEscape.clock_depth_holding
#check @EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_four
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_four
#check @EndgameChess.Rules.KRKFourPlyEscape.weak_five_to_four
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_five_to_four
#check @EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_five
#print axioms EndgameChess.Rules.KRKFourPlyEscape.weak_interior_not_five
#check @EndgameChess.Rules.KRKFourPlyEscape.mate_depth_lower
#print axioms EndgameChess.Rules.KRKFourPlyEscape.mate_depth_lower
#check @EndgameChess.Rules.KRKLastReply.ready_neighbour_unique
#print axioms EndgameChess.Rules.KRKLastReply.ready_neighbour_unique
#check @EndgameChess.Rules.KRKLastReply.model_last_iff
#print axioms EndgameChess.Rules.KRKLastReply.model_last_iff
#check @EndgameChess.Rules.KRKLastReply.rule_two_iff
#print axioms EndgameChess.Rules.KRKLastReply.rule_two_iff
#check @EndgameChess.Rules.KRKLastReply.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_force_iff
#check @EndgameChess.Rules.KRKLastReply.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_actual_iff
#check @EndgameChess.Rules.KRKLastReply.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_hold_iff
#check @EndgameChess.Rules.KRKLastReply.high_clock_exact_two
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_exact_two
#check @EndgameChess.Rules.KRKLastReply.weak_two_iff
#print axioms EndgameChess.Rules.KRKLastReply.weak_two_iff
#check @EndgameChess.Rules.KRKLastReply.strong_two_to_one
#print axioms EndgameChess.Rules.KRKLastReply.strong_two_to_one
#check @EndgameChess.Rules.KRKLastReply.weak_three_iff
#print axioms EndgameChess.Rules.KRKLastReply.weak_three_iff
#check @EndgameChess.Rules.KRKLastReply.weak_move_eq
#print axioms EndgameChess.Rules.KRKLastReply.weak_move_eq
#check @EndgameChess.Rules.KRKLastReply.lone_step_legal
#print axioms EndgameChess.Rules.KRKLastReply.lone_step_legal
#check @EndgameChess.Rules.KRKLastReply.unique_legal_reply
#print axioms EndgameChess.Rules.KRKLastReply.unique_legal_reply
#check @EndgameChess.Rules.KRKLastReply.weak_safe_quiet
#print axioms EndgameChess.Rules.KRKLastReply.weak_safe_quiet
#check @EndgameChess.Rules.KRKLastReply.no_claim_at_unique_reply
#print axioms EndgameChess.Rules.KRKLastReply.no_claim_at_unique_reply
#check @EndgameChess.Rules.KRKLastReply.high_clock_actual_key_iff
#print axioms EndgameChess.Rules.KRKLastReply.high_clock_actual_key_iff
#check @EndgameChess.Rules.KRKMateGeometry.horizontal_edge
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_edge
#check @EndgameChess.Rules.KRKMateGeometry.horizontal_necessity
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_necessity
#check @EndgameChess.Rules.KRKMateGeometry.horizontal_sufficiency
#print axioms EndgameChess.Rules.KRKMateGeometry.horizontal_sufficiency
#check @EndgameChess.Rules.KRKMateGeometry.mate_iff_terminal
#print axioms EndgameChess.Rules.KRKMateGeometry.mate_iff_terminal
#check @EndgameChess.Rules.KRKMateGeometry.king_step_not_mate
#print axioms EndgameChess.Rules.KRKMateGeometry.king_step_not_mate
#check @EndgameChess.Rules.KRKMateGeometry.kernel_mate_model
#print axioms EndgameChess.Rules.KRKMateGeometry.kernel_mate_model
#check @EndgameChess.Rules.KRKMateGeometry.kernel_mate_iff
#print axioms EndgameChess.Rules.KRKMateGeometry.kernel_mate_iff
#check @EndgameChess.Rules.KRKMatingMove.castle_not_mate
#print axioms EndgameChess.Rules.KRKMatingMove.castle_not_mate
#check @EndgameChess.Rules.KRKMatingMove.king_move_not_mate
#print axioms EndgameChess.Rules.KRKMatingMove.king_move_not_mate
#check @EndgameChess.Rules.KRKMatingMove.mating_source
#print axioms EndgameChess.Rules.KRKMatingMove.mating_source
#check @EndgameChess.Rules.KRKMatingMove.rook_move_model
#print axioms EndgameChess.Rules.KRKMatingMove.rook_move_model
#check @EndgameChess.Rules.KRKNativeFrame.Frame.eq_iff
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.eq_iff
#check @EndgameChess.Rules.KRKNativeFrame.Frame.ne_iff
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.ne_iff
#check @EndgameChess.Rules.KRKNativeFrame.Frame.preimage_eq
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.preimage_eq
#check @EndgameChess.Rules.KRKNativeFrame.Frame.map_step
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.map_step
#check @EndgameChess.Rules.KRKNativeFrame.Frame.map_inverse
#print axioms EndgameChess.Rules.KRKNativeFrame.Frame.map_inverse
#check @EndgameChess.Rules.KRKNativeFrame.bottomFrame_spec
#print axioms EndgameChess.Rules.KRKNativeFrame.bottomFrame_spec
#check @EndgameChess.Rules.KRKNativeFrame.normalize_spec
#print axioms EndgameChess.Rules.KRKNativeFrame.normalize_spec
#check @EndgameChess.Rules.KRKNearKingBarrier.king_history_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.king_history_iff
#check @EndgameChess.Rules.KRKNearKingBarrier.rook_history_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.rook_history_iff
#check @EndgameChess.Rules.KRKNearKingBarrier.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_force_iff
#check @EndgameChess.Rules.KRKNearKingBarrier.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_actual_iff
#check @EndgameChess.Rules.KRKNearKingBarrier.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_hold_iff
#check @EndgameChess.Rules.KRKNearKingBarrier.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKNearKingBarrier.high_clock_exact_three
#check @EndgameChess.Rules.KRKNearSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_geometry
#check @EndgameChess.Rules.KRKNearSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_reply_distance
#check @EndgameChess.Rules.KRKNearSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.last_slots_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.flat_return_legal
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.flat_return_legal
#check @EndgameChess.Rules.KRKNearSlotBarriers.slot_sees_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.slot_sees_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.king_history_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.rook_history_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_force_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_actual_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_hold_iff
#check @EndgameChess.Rules.KRKNearSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKNearSlotBarriers.high_clock_distance_cases
#check @EndgameChess.Rules.KRKNearWeakBand.neighbour_cases
#print axioms EndgameChess.Rules.KRKNearWeakBand.neighbour_cases
#check @EndgameChess.Rules.KRKNearWeakBand.necessary
#print axioms EndgameChess.Rules.KRKNearWeakBand.necessary
#check @EndgameChess.Rules.KRKNearWeakBand.sufficient
#print axioms EndgameChess.Rules.KRKNearWeakBand.sufficient
#check @EndgameChess.Rules.KRKNearWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_force_iff
#check @EndgameChess.Rules.KRKNearWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_actual_iff
#check @EndgameChess.Rules.KRKNearWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_hold_iff
#check @EndgameChess.Rules.KRKNearWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_draw_iff
#check @EndgameChess.Rules.KRKNearWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKNearWeakBand.high_clock_distance_cases
#check @EndgameChess.Rules.KRKNineEdge.clear_iff
#print axioms EndgameChess.Rules.KRKNineEdge.clear_iff
#check @EndgameChess.Rules.KRKNineEdge.kernel_nine_iff
#print axioms EndgameChess.Rules.KRKNineEdge.kernel_nine_iff
#check @EndgameChess.Rules.KRKNineEntry.eight_entry_move
#print axioms EndgameChess.Rules.KRKNineEntry.eight_entry_move
#check @EndgameChess.Rules.KRKNineGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKNineGeometry.entry_sufficient
#check @EndgameChess.Rules.KRKNineGeometry.sufficient
#print axioms EndgameChess.Rules.KRKNineGeometry.sufficient
#check @EndgameChess.Rules.KRKNineGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKNineGeometry.entry_necessary
#check @EndgameChess.Rules.KRKNineGeometry.necessary
#print axioms EndgameChess.Rules.KRKNineGeometry.necessary
#check @EndgameChess.Rules.KRKNineGeometry.kernel_nine_iff
#print axioms EndgameChess.Rules.KRKNineGeometry.kernel_nine_iff
#check @EndgameChess.Rules.KRKNineGeometry.frame_map
#print axioms EndgameChess.Rules.KRKNineGeometry.frame_map
#check @EndgameChess.Rules.KRKNineGeometry.king_step_clear
#print axioms EndgameChess.Rules.KRKNineGeometry.king_step_clear
#check @EndgameChess.Rules.KRKNineGeometry.rook_step_clear
#print axioms EndgameChess.Rules.KRKNineGeometry.rook_step_clear
#check @EndgameChess.Rules.KRKNineInner.horizontal_shape
#print axioms EndgameChess.Rules.KRKNineInner.horizontal_shape
#check @EndgameChess.Rules.KRKNineInner.global_region_iff
#print axioms EndgameChess.Rules.KRKNineInner.global_region_iff
#check @EndgameChess.Rules.KRKNineInner.king_points_iff
#print axioms EndgameChess.Rules.KRKNineInner.king_points_iff
#check @EndgameChess.Rules.KRKNineInner.rook_line_necessary
#print axioms EndgameChess.Rules.KRKNineInner.rook_line_necessary
#check @EndgameChess.Rules.KRKNineInner.rook_destination
#print axioms EndgameChess.Rules.KRKNineInner.rook_destination
#check @EndgameChess.Rules.KRKNineInner.rook_rays_necessary
#print axioms EndgameChess.Rules.KRKNineInner.rook_rays_necessary
#check @EndgameChess.Rules.KRKNineInner.canonical_rook_clear
#print axioms EndgameChess.Rules.KRKNineInner.canonical_rook_clear
#check @EndgameChess.Rules.KRKNineInner.clear_iff
#print axioms EndgameChess.Rules.KRKNineInner.clear_iff
#check @EndgameChess.Rules.KRKNineInner.kernel_nine_iff
#print axioms EndgameChess.Rules.KRKNineInner.kernel_nine_iff
#check @EndgameChess.Rules.KRKNineInner.kernel_exact_nine
#print axioms EndgameChess.Rules.KRKNineInner.kernel_exact_nine
#check @EndgameChess.Rules.KRKNineInnerBoundary.inner_region
#print axioms EndgameChess.Rules.KRKNineInnerBoundary.inner_region
#check @EndgameChess.Rules.KRKNineInnerBoundary.rook_two_zero_high
#print axioms EndgameChess.Rules.KRKNineInnerBoundary.rook_two_zero_high
#check @EndgameChess.Rules.KRKNineInnerBoundary.rook_two_three_right_high
#print axioms EndgameChess.Rules.KRKNineInnerBoundary.rook_two_three_right_high
#check @EndgameChess.Rules.KRKNineMiddleLow.eight_no_high_king
#print axioms EndgameChess.Rules.KRKNineMiddleLow.eight_no_high_king
#check @EndgameChess.Rules.KRKNineMiddleLow.eight_low_necessary
#print axioms EndgameChess.Rules.KRKNineMiddleLow.eight_low_necessary
#check @EndgameChess.Rules.KRKNineMiddleLow.no_nine
#print axioms EndgameChess.Rules.KRKNineMiddleLow.no_nine
#check @EndgameChess.Rules.KRKNineMiddleLow.king_two_three_necessary
#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_necessary
#check @EndgameChess.Rules.KRKNineMiddleLow.four_five_eight_clear
#print axioms EndgameChess.Rules.KRKNineMiddleLow.four_five_eight_clear
#check @EndgameChess.Rules.KRKNineMiddleLow.king_two_three_sufficient
#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_sufficient
#check @EndgameChess.Rules.KRKNineMiddleLow.king_two_three_iff
#print axioms EndgameChess.Rules.KRKNineMiddleLow.king_two_three_iff
#check @EndgameChess.Rules.KRKNineNearDiagonal.no_nine
#print axioms EndgameChess.Rules.KRKNineNearDiagonal.no_nine
#check @EndgameChess.Rules.KRKNineNearStrip.rook_line_necessary
#print axioms EndgameChess.Rules.KRKNineNearStrip.rook_line_necessary
#check @EndgameChess.Rules.KRKNineNearStrip.rook_destination
#print axioms EndgameChess.Rules.KRKNineNearStrip.rook_destination
#check @EndgameChess.Rules.KRKNineNearStrip.necessary
#print axioms EndgameChess.Rules.KRKNineNearStrip.necessary
#check @EndgameChess.Rules.KRKNineNearStrip.sufficient
#print axioms EndgameChess.Rules.KRKNineNearStrip.sufficient
#check @EndgameChess.Rules.KRKNineNearStrip.kernel_nine_iff
#print axioms EndgameChess.Rules.KRKNineNearStrip.kernel_nine_iff
#check @EndgameChess.Rules.KRKNineNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKNineNearStrip.clear_iff
#check @EndgameChess.Rules.KRKNineNearStrip.kernel_exact_nine
#print axioms EndgameChess.Rules.KRKNineNearStrip.kernel_exact_nine
#check @EndgameChess.Rules.KRKNineNearStripHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.entry_certificate
#check @EndgameChess.Rules.KRKNineNearStripHistory.sufficient
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.sufficient
#check @EndgameChess.Rules.KRKNineNearStripHistory.necessary
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.necessary
#check @EndgameChess.Rules.KRKNineNearStripHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKNineNearStripHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKNineNearStripHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKNineNearStripHistory.exact_nine
#print axioms EndgameChess.Rules.KRKNineNearStripHistory.exact_nine
#check @EndgameChess.Rules.KRKNinePlyExact.necessary
#print axioms EndgameChess.Rules.KRKNinePlyExact.necessary
#check @EndgameChess.Rules.KRKNinePlyExact.rule_nine_iff
#print axioms EndgameChess.Rules.KRKNinePlyExact.rule_nine_iff
#check @EndgameChess.Rules.KRKNinePlyExact.strong_ten_nine
#print axioms EndgameChess.Rules.KRKNinePlyExact.strong_ten_nine
#check @EndgameChess.Rules.KRKNinePlyExact.weak_eleven_ten
#print axioms EndgameChess.Rules.KRKNinePlyExact.weak_eleven_ten
#check @EndgameChess.Rules.KRKNinePlyExact.high_clock_distance_split
#print axioms EndgameChess.Rules.KRKNinePlyExact.high_clock_distance_split
#check @EndgameChess.Rules.KRKNinePlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKNinePlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKNinePlyHistory.clear_geometry
#print axioms EndgameChess.Rules.KRKNinePlyHistory.clear_geometry
#check @EndgameChess.Rules.KRKNinePlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKNinePlyHistory.clear_kernel
#check @EndgameChess.Rules.KRKNinePlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKNinePlyHistory.entry_certificate
#check @EndgameChess.Rules.KRKNinePlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKNinePlyHistory.sufficient
#check @EndgameChess.Rules.KRKNinePlyHistory.necessary
#print axioms EndgameChess.Rules.KRKNinePlyHistory.necessary
#check @EndgameChess.Rules.KRKNinePlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKNinePlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKNinePlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKNinePlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKNineSecondBoundary.no_nine
#print axioms EndgameChess.Rules.KRKNineSecondBoundary.no_nine
#check @EndgameChess.Rules.KRKNineSecondLeft.no_nine
#print axioms EndgameChess.Rules.KRKNineSecondLeft.no_nine
#check @EndgameChess.Rules.KRKNineSlots.seven_test_rank
#print axioms EndgameChess.Rules.KRKNineSlots.seven_test_rank
#check @EndgameChess.Rules.KRKNineSlots.edge_rank
#print axioms EndgameChess.Rules.KRKNineSlots.edge_rank
#check @EndgameChess.Rules.KRKNineSlots.region_rank
#print axioms EndgameChess.Rules.KRKNineSlots.region_rank
#check @EndgameChess.Rules.KRKNineSlots.region_point
#print axioms EndgameChess.Rules.KRKNineSlots.region_point
#check @EndgameChess.Rules.KRKNineUpperEntries.near_entry
#print axioms EndgameChess.Rules.KRKNineUpperEntries.near_entry
#check @EndgameChess.Rules.KRKNineUpperEntries.second_entry
#print axioms EndgameChess.Rules.KRKNineUpperEntries.second_entry
#check @EndgameChess.Rules.KRKOppositionHistory.opposition_step_cases
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_step_cases
#check @EndgameChess.Rules.KRKOppositionHistory.west_legal
#print axioms EndgameChess.Rules.KRKOppositionHistory.west_legal
#check @EndgameChess.Rules.KRKOppositionHistory.east_legal
#print axioms EndgameChess.Rules.KRKOppositionHistory.east_legal
#check @EndgameChess.Rules.KRKOppositionHistory.weak_force_data
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_force_data
#check @EndgameChess.Rules.KRKOppositionHistory.weak_force_no_claim
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_force_no_claim
#check @EndgameChess.Rules.KRKOppositionHistory.branch_necessary
#print axioms EndgameChess.Rules.KRKOppositionHistory.branch_necessary
#check @EndgameChess.Rules.KRKOppositionHistory.opposition_necessary
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_necessary
#check @EndgameChess.Rules.KRKOppositionHistory.branch_certificate
#print axioms EndgameChess.Rules.KRKOppositionHistory.branch_certificate
#check @EndgameChess.Rules.KRKOppositionHistory.opposition_sufficient
#print axioms EndgameChess.Rules.KRKOppositionHistory.opposition_sufficient
#check @EndgameChess.Rules.KRKOppositionHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKOppositionHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKOppositionHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKOppositionHistory.high_clock_exact_four
#print axioms EndgameChess.Rules.KRKOppositionHistory.high_clock_exact_four
#check @EndgameChess.Rules.KRKOppositionHistory.weak_material_after
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_material_after
#check @EndgameChess.Rules.KRKOppositionHistory.weak_keys_ne
#print axioms EndgameChess.Rules.KRKOppositionHistory.weak_keys_ne
#check @EndgameChess.Rules.KRKOppositionHistory.append_query
#print axioms EndgameChess.Rules.KRKOppositionHistory.append_query
#check @EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged_of_last
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged_of_last
#check @EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_queries_unchanged
#check @EndgameChess.Rules.KRKOppositionHistory.ray_append_iff_of_last
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_append_iff_of_last
#check @EndgameChess.Rules.KRKOppositionHistory.ray_append_iff
#print axioms EndgameChess.Rules.KRKOppositionHistory.ray_append_iff
#check @EndgameChess.Rules.KRKOrdinaryEntry.king_legal
#print axioms EndgameChess.Rules.KRKOrdinaryEntry.king_legal
#check @EndgameChess.Rules.KRKOrdinaryEntry.rook_legal
#print axioms EndgameChess.Rules.KRKOrdinaryEntry.rook_legal
#check @EndgameChess.Rules.KRKRookRayBarriers.ray_last_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.ray_last_iff
#check @EndgameChess.Rules.KRKRookRayBarriers.ray_sees_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.ray_sees_iff
#check @EndgameChess.Rules.KRKRookRayBarriers.return_legal
#print axioms EndgameChess.Rules.KRKRookRayBarriers.return_legal
#check @EndgameChess.Rules.KRKRookRayBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_force_iff
#check @EndgameChess.Rules.KRKRookRayBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_actual_iff
#check @EndgameChess.Rules.KRKRookRayBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_hold_iff
#check @EndgameChess.Rules.KRKRookRayBarriers.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKRookRayBarriers.high_clock_exact_three
#check @EndgameChess.Rules.KRKSecondOppositionHistory.second_necessary
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.second_necessary
#check @EndgameChess.Rules.KRKSecondOppositionHistory.second_sufficient
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.second_sufficient
#check @EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_exact_four
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.high_clock_exact_four
#check @EndgameChess.Rules.KRKSecondOppositionHistory.king_queries_unchanged
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.king_queries_unchanged
#check @EndgameChess.Rules.KRKSecondOppositionHistory.king_append_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.king_append_iff
#check @EndgameChess.Rules.KRKSecondOppositionHistory.west_ray_append_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_ray_append_iff
#check @EndgameChess.Rules.KRKSecondOppositionHistory.west_alternatives_append_iff
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_alternatives_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Second.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Second.clear_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Second.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Second.history_append_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.slot_geometry
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_geometry
#check @EndgameChess.Rules.KRKSecondStrongSlots.slot_reply_distance
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_reply_distance
#check @EndgameChess.Rules.KRKSecondStrongSlots.last_slots_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.last_slots_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.flat_return_legal
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.flat_return_legal
#check @EndgameChess.Rules.KRKSecondStrongSlots.slot_sees_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.slot_sees_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.king_history_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.king_history_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.rook_history_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.rook_history_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.immediate_second_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.immediate_second_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_force_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_actual_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_hold_iff
#check @EndgameChess.Rules.KRKSecondStrongSlots.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSecondStrongSlots.high_clock_distance_cases
#check @EndgameChess.Rules.KRKSecondWeakBand.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_force_iff
#check @EndgameChess.Rules.KRKSecondWeakBand.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_actual_iff
#check @EndgameChess.Rules.KRKSecondWeakBand.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_hold_iff
#check @EndgameChess.Rules.KRKSecondWeakBand.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_draw_iff
#check @EndgameChess.Rules.KRKSecondWeakBand.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSecondWeakBand.high_clock_distance_cases
#check @EndgameChess.Rules.KRKSecondOppositionHistory.west_necessary
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_necessary
#check @EndgameChess.Rules.KRKSecondOppositionHistory.west_certificate
#print axioms EndgameChess.Rules.KRKSecondOppositionHistory.west_certificate
#check @EndgameChess.Rules.KRKSevenCorner.live_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.live_iff
#check @EndgameChess.Rules.KRKSevenCorner.frame_f
#print axioms EndgameChess.Rules.KRKSevenCorner.frame_f
#check @EndgameChess.Rules.KRKSevenCorner.frame_r
#print axioms EndgameChess.Rules.KRKSevenCorner.frame_r
#check @EndgameChess.Rules.KRKSevenCorner.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.global_region_iff
#check @EndgameChess.Rules.KRKSevenCorner.region_point
#print axioms EndgameChess.Rules.KRKSevenCorner.region_point
#check @EndgameChess.Rules.KRKSevenCorner.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.king_points_iff
#check @EndgameChess.Rules.KRKSevenCorner.rook_line_necessary
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_line_necessary
#check @EndgameChess.Rules.KRKSevenCorner.rook_destination
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_destination
#check @EndgameChess.Rules.KRKSevenCorner.rook_rays_necessary
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_rays_necessary
#check @EndgameChess.Rules.KRKSevenCorner.canonical_rook_clear
#print axioms EndgameChess.Rules.KRKSevenCorner.canonical_rook_clear
#check @EndgameChess.Rules.KRKSevenCorner.rook_entries_sufficient
#print axioms EndgameChess.Rules.KRKSevenCorner.rook_entries_sufficient
#check @EndgameChess.Rules.KRKSevenCorner.immediate_entries
#print axioms EndgameChess.Rules.KRKSevenCorner.immediate_entries
#check @EndgameChess.Rules.KRKSevenCorner.clear_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.clear_iff
#check @EndgameChess.Rules.KRKSevenCorner.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKSevenCorner.kernel_seven_iff
#check @EndgameChess.Rules.KRKSevenEntry.six_entry_move
#print axioms EndgameChess.Rules.KRKSevenEntry.six_entry_move
#check @EndgameChess.Rules.KRKSevenGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKSevenGeometry.entry_sufficient
#check @EndgameChess.Rules.KRKSevenGeometry.sufficient
#print axioms EndgameChess.Rules.KRKSevenGeometry.sufficient
#check @EndgameChess.Rules.KRKSevenGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKSevenGeometry.entry_necessary
#check @EndgameChess.Rules.KRKSevenGeometry.necessary
#print axioms EndgameChess.Rules.KRKSevenGeometry.necessary
#check @EndgameChess.Rules.KRKSevenGeometry.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKSevenGeometry.kernel_seven_iff
#check @EndgameChess.Rules.KRKSevenInner.inner_entry_necessary
#print axioms EndgameChess.Rules.KRKSevenInner.inner_entry_necessary
#check @EndgameChess.Rules.KRKSevenInner.horizontal_line_necessary
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_line_necessary
#check @EndgameChess.Rules.KRKSevenInner.horizontal_line_sufficient
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_line_sufficient
#check @EndgameChess.Rules.KRKSevenInner.horizontal_properties
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_properties
#check @EndgameChess.Rules.KRKSevenInner.horizontal_rook_clear
#print axioms EndgameChess.Rules.KRKSevenInner.horizontal_rook_clear
#check @EndgameChess.Rules.KRKSevenInner.necessary
#print axioms EndgameChess.Rules.KRKSevenInner.necessary
#check @EndgameChess.Rules.KRKSevenInner.swap_clear_iff
#print axioms EndgameChess.Rules.KRKSevenInner.swap_clear_iff
#check @EndgameChess.Rules.KRKSevenInner.sufficient
#print axioms EndgameChess.Rules.KRKSevenInner.sufficient
#check @EndgameChess.Rules.KRKSevenInner.clear_iff
#print axioms EndgameChess.Rules.KRKSevenInner.clear_iff
#check @EndgameChess.Rules.KRKSevenInner.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKSevenInner.kernel_seven_iff
#check @EndgameChess.Rules.KRKSevenMiddle.kernel_seven_five_iff
#print axioms EndgameChess.Rules.KRKSevenMiddle.kernel_seven_five_iff
#check @EndgameChess.Rules.KRKSevenMiddle.bottom_clear_iff
#print axioms EndgameChess.Rules.KRKSevenMiddle.bottom_clear_iff
#check @EndgameChess.Rules.KRKSevenMiddle.low_rook_clear_iff
#print axioms EndgameChess.Rules.KRKSevenMiddle.low_rook_clear_iff
#check @EndgameChess.Rules.KRKSevenNear.shape_iff
#print axioms EndgameChess.Rules.KRKSevenNear.shape_iff
#check @EndgameChess.Rules.KRKSevenNear.king_far
#print axioms EndgameChess.Rules.KRKSevenNear.king_far
#check @EndgameChess.Rules.KRKSevenNear.slot_properties
#print axioms EndgameChess.Rules.KRKSevenNear.slot_properties
#check @EndgameChess.Rules.KRKSevenNear.diagonal_live
#print axioms EndgameChess.Rules.KRKSevenNear.diagonal_live
#check @EndgameChess.Rules.KRKSevenNear.slot_live
#print axioms EndgameChess.Rules.KRKSevenNear.slot_live
#check @EndgameChess.Rules.KRKSevenNear.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenNear.global_region_iff
#check @EndgameChess.Rules.KRKSevenNear.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenNear.king_points_iff
#check @EndgameChess.Rules.KRKSevenNear.low_reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.low_reach_iff
#check @EndgameChess.Rules.KRKSevenNear.side_reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.side_reach_iff
#check @EndgameChess.Rules.KRKSevenNear.high_reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.high_reach_iff
#check @EndgameChess.Rules.KRKSevenNear.reach_iff
#print axioms EndgameChess.Rules.KRKSevenNear.reach_iff
#check @EndgameChess.Rules.KRKSevenNear.rook_rays_iff
#print axioms EndgameChess.Rules.KRKSevenNear.rook_rays_iff
#check @EndgameChess.Rules.KRKSevenNear.clear_iff
#print axioms EndgameChess.Rules.KRKSevenNear.clear_iff
#check @EndgameChess.Rules.KRKSevenNear.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKSevenNear.kernel_seven_iff
#check @EndgameChess.Rules.KRKSevenPlyExact.necessary
#print axioms EndgameChess.Rules.KRKSevenPlyExact.necessary
#check @EndgameChess.Rules.KRKSevenPlyExact.rule_seven_iff
#print axioms EndgameChess.Rules.KRKSevenPlyExact.rule_seven_iff
#check @EndgameChess.Rules.KRKSevenPlyExact.strong_eight_seven
#print axioms EndgameChess.Rules.KRKSevenPlyExact.strong_eight_seven
#check @EndgameChess.Rules.KRKSevenPlyExact.weak_nine_eight
#print axioms EndgameChess.Rules.KRKSevenPlyExact.weak_nine_eight
#check @EndgameChess.Rules.KRKSevenPlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKSevenPlyExact.distance_cases
#check @EndgameChess.Rules.KRKSevenPlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.entry_certificate
#check @EndgameChess.Rules.KRKSevenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.sufficient
#check @EndgameChess.Rules.KRKSevenPlyHistory.entry_kernel
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.entry_kernel
#check @EndgameChess.Rules.KRKSevenPlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.clear_kernel
#check @EndgameChess.Rules.KRKSevenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.necessary
#check @EndgameChess.Rules.KRKSevenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKSevenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKSevenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKSevenPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSevenPlyHistory.high_clock_distance_cases
#check @EndgameChess.Rules.KRKSevenPrefix.first_occurrences_root
#print axioms EndgameChess.Rules.KRKSevenPrefix.first_occurrences_root
#check @EndgameChess.Rules.KRKSevenPrefix.second_occurrences_root
#print axioms EndgameChess.Rules.KRKSevenPrefix.second_occurrences_root
#check @EndgameChess.Rules.KRKSevenPrefix.fourth_entry_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.fourth_entry_root_iff
#check @EndgameChess.Rules.KRKSevenPrefix.inner_clear_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.inner_clear_root_iff
#check @EndgameChess.Rules.KRKSevenPrefix.weak_after_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.weak_after_root_iff
#check @EndgameChess.Rules.KRKSevenPrefix.strong_clear_root_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.strong_clear_root_iff
#check @EndgameChess.Rules.KRKSevenPrefix.six_append_iff
#print axioms EndgameChess.Rules.KRKSevenPrefix.six_append_iff
#check @EndgameChess.Rules.KRKSevenReach.region_weak_domain
#print axioms EndgameChess.Rules.KRKSevenReach.region_weak_domain
#check @EndgameChess.Rules.KRKSevenReach.region_interior_distance
#print axioms EndgameChess.Rules.KRKSevenReach.region_interior_distance
#check @EndgameChess.Rules.KRKSevenReach.weak_domain
#print axioms EndgameChess.Rules.KRKSevenReach.weak_domain
#check @EndgameChess.Rules.KRKSevenReach.interior_king_near
#print axioms EndgameChess.Rules.KRKSevenReach.interior_king_near
#check @EndgameChess.Rules.KRKSevenReach.frame_map
#print axioms EndgameChess.Rules.KRKSevenReach.frame_map
#check @EndgameChess.Rules.KRKSevenReach.king_step_clear
#print axioms EndgameChess.Rules.KRKSevenReach.king_step_clear
#check @EndgameChess.Rules.KRKSevenReach.rook_step_clear
#print axioms EndgameChess.Rules.KRKSevenReach.rook_step_clear
#check @EndgameChess.Rules.KRKSevenSecond.shape_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.shape_iff
#check @EndgameChess.Rules.KRKSevenSecond.global_region_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.global_region_iff
#check @EndgameChess.Rules.KRKSevenSecond.frame_f
#print axioms EndgameChess.Rules.KRKSevenSecond.frame_f
#check @EndgameChess.Rules.KRKSevenSecond.frame_r
#print axioms EndgameChess.Rules.KRKSevenSecond.frame_r
#check @EndgameChess.Rules.KRKSevenSecond.properties
#print axioms EndgameChess.Rules.KRKSevenSecond.properties
#check @EndgameChess.Rules.KRKSevenSecond.king_points_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.king_points_iff
#check @EndgameChess.Rules.KRKSevenSecond.rook_destination
#print axioms EndgameChess.Rules.KRKSevenSecond.rook_destination
#check @EndgameChess.Rules.KRKSevenSecond.rook_rays_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.rook_rays_iff
#check @EndgameChess.Rules.KRKSevenSecond.clear_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.clear_iff
#check @EndgameChess.Rules.KRKSevenSecond.kernel_seven_iff
#print axioms EndgameChess.Rules.KRKSevenSecond.kernel_seven_iff
#check @EndgameChess.Rules.KRKSevenSlots.region_bounds
#print axioms EndgameChess.Rules.KRKSevenSlots.region_bounds
#check @EndgameChess.Rules.KRKSevenSlots.region_point
#print axioms EndgameChess.Rules.KRKSevenSlots.region_point
#check @EndgameChess.Rules.KRKSixCorner.blocked_or_near
#print axioms EndgameChess.Rules.KRKSixCorner.blocked_or_near
#check @EndgameChess.Rules.KRKSixCorner.live_not_diagonal_rook
#print axioms EndgameChess.Rules.KRKSixCorner.live_not_diagonal_rook
#check @EndgameChess.Rules.KRKSixCorner.corner_six_necessary
#print axioms EndgameChess.Rules.KRKSixCorner.corner_six_necessary
#check @EndgameChess.Rules.KRKSixCorner.region_swap
#print axioms EndgameChess.Rules.KRKSixCorner.region_swap
#check @EndgameChess.Rules.KRKSixCorner.region_excludes_inward
#print axioms EndgameChess.Rules.KRKSixCorner.region_excludes_inward
#check @EndgameChess.Rules.KRKSixCorner.region_south_five
#print axioms EndgameChess.Rules.KRKSixCorner.region_south_five
#check @EndgameChess.Rules.KRKSixCorner.region_replies
#print axioms EndgameChess.Rules.KRKSixCorner.region_replies
#check @EndgameChess.Rules.KRKSixCorner.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixCorner.kernel_six_iff
#check @EndgameChess.Rules.KRKSixGeometry.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixGeometry.kernel_six_iff
#check @EndgameChess.Rules.KRKSixGeometry.strong_six_five
#print axioms EndgameChess.Rules.KRKSixGeometry.strong_six_five
#check @EndgameChess.Rules.KRKSixGeometry.weak_seven_six
#print axioms EndgameChess.Rules.KRKSixGeometry.weak_seven_six
#check @EndgameChess.Rules.KRKSixGlobal.canonical_necessary
#print axioms EndgameChess.Rules.KRKSixGlobal.canonical_necessary
#check @EndgameChess.Rules.KRKSixGlobal.canonical_sufficient
#print axioms EndgameChess.Rules.KRKSixGlobal.canonical_sufficient
#check @EndgameChess.Rules.KRKSixGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKSixGlobal.edge_clear_iff
#check @EndgameChess.Rules.KRKSixGlobal.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixGlobal.kernel_six_iff
#check @EndgameChess.Rules.KRKSixGlobal.kernel_exact_six_iff
#print axioms EndgameChess.Rules.KRKSixGlobal.kernel_exact_six_iff
#check @EndgameChess.Rules.KRKSixInterior.strip_escape
#print axioms EndgameChess.Rules.KRKSixInterior.strip_escape
#check @EndgameChess.Rules.KRKSixInterior.every_map
#print axioms EndgameChess.Rules.KRKSixInterior.every_map
#check @EndgameChess.Rules.KRKSixInterior.interior_corner_necessary
#print axioms EndgameChess.Rules.KRKSixInterior.interior_corner_necessary
#check @EndgameChess.Rules.KRKSixInterior.weak_six_interior_corner
#print axioms EndgameChess.Rules.KRKSixInterior.weak_six_interior_corner
#check @EndgameChess.Rules.KRKSixInteriorHolding.strong_eight_interior_corner
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.strong_eight_interior_corner
#check @EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_necessary
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_necessary
#check @EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_holding
#print axioms EndgameChess.Rules.KRKSixInteriorHolding.high_clock_interior_holding
#check @EndgameChess.Rules.KRKSixInwardCorner.near_from_step
#print axioms EndgameChess.Rules.KRKSixInwardCorner.near_from_step
#check @EndgameChess.Rules.KRKSixInwardCorner.horizontal_necessary
#print axioms EndgameChess.Rules.KRKSixInwardCorner.horizontal_necessary
#check @EndgameChess.Rules.KRKSixInwardCorner.upper_escape
#print axioms EndgameChess.Rules.KRKSixInwardCorner.upper_escape
#check @EndgameChess.Rules.KRKSixInwardCorner.no_five_diagonal
#print axioms EndgameChess.Rules.KRKSixInwardCorner.no_five_diagonal
#check @EndgameChess.Rules.KRKSixInwardCorner.necessary
#print axioms EndgameChess.Rules.KRKSixInwardCorner.necessary
#check @EndgameChess.Rules.KRKSixInwardCorner.horizontal_replies
#print axioms EndgameChess.Rules.KRKSixInwardCorner.horizontal_replies
#check @EndgameChess.Rules.KRKSixInwardCorner.replies_of_region
#print axioms EndgameChess.Rules.KRKSixInwardCorner.replies_of_region
#check @EndgameChess.Rules.KRKSixInwardCorner.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixInwardCorner.kernel_six_iff
#check @EndgameChess.Rules.KRKSixInwardCorner.region_clear
#print axioms EndgameChess.Rules.KRKSixInwardCorner.region_clear
#check @EndgameChess.Rules.KRKSixInwardCorner.map_six
#print axioms EndgameChess.Rules.KRKSixInwardCorner.map_six
#check @EndgameChess.Rules.KRKSixInwardCorner.inner_sym_spec
#print axioms EndgameChess.Rules.KRKSixInwardCorner.inner_sym_spec
#check @EndgameChess.Rules.KRKSixInwardCorner.global_kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixInwardCorner.global_kernel_six_iff
#check @EndgameChess.Rules.KRKSixInwardCorner.global_kernel_exact_six
#print axioms EndgameChess.Rules.KRKSixInwardCorner.global_kernel_exact_six
#check @EndgameChess.Rules.KRKSixMiddle.covered_or_five
#print axioms EndgameChess.Rules.KRKSixMiddle.covered_or_five
#check @EndgameChess.Rules.KRKSixMiddle.central_six_necessary
#print axioms EndgameChess.Rules.KRKSixMiddle.central_six_necessary
#check @EndgameChess.Rules.KRKSixMiddle.kernel_six_four_iff
#print axioms EndgameChess.Rules.KRKSixMiddle.kernel_six_four_iff
#check @EndgameChess.Rules.KRKSixNear.necessary
#print axioms EndgameChess.Rules.KRKSixNear.necessary
#check @EndgameChess.Rules.KRKSixNear.extra_replies
#print axioms EndgameChess.Rules.KRKSixNear.extra_replies
#check @EndgameChess.Rules.KRKSixNear.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixNear.kernel_six_iff
#check @EndgameChess.Rules.KRKSixNear.kernel_exact_six_iff
#print axioms EndgameChess.Rules.KRKSixNear.kernel_exact_six_iff
#check @EndgameChess.Rules.KRKSixPlyExact.necessary
#print axioms EndgameChess.Rules.KRKSixPlyExact.necessary
#check @EndgameChess.Rules.KRKSixPlyExact.rule_six_iff
#print axioms EndgameChess.Rules.KRKSixPlyExact.rule_six_iff
#check @EndgameChess.Rules.KRKSixPlyExact.weak_seven_six
#print axioms EndgameChess.Rules.KRKSixPlyExact.weak_seven_six
#check @EndgameChess.Rules.KRKSixPlyHistory.child_five_certificate
#print axioms EndgameChess.Rules.KRKSixPlyHistory.child_five_certificate
#check @EndgameChess.Rules.KRKSixPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKSixPlyHistory.necessary
#check @EndgameChess.Rules.KRKSixPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKSixPlyHistory.sufficient
#check @EndgameChess.Rules.KRKSixPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKSixPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKSixPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKSixPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKSixPlyHistory.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKSixPlyHistory.high_clock_distance_cases
#check @EndgameChess.Rules.KRKSixSecond.necessary
#print axioms EndgameChess.Rules.KRKSixSecond.necessary
#check @EndgameChess.Rules.KRKSixSecond.region_replies
#print axioms EndgameChess.Rules.KRKSixSecond.region_replies
#check @EndgameChess.Rules.KRKSixSecond.kernel_six_iff
#print axioms EndgameChess.Rules.KRKSixSecond.kernel_six_iff
#check @EndgameChess.Rules.KRKSixSecond.new_geometry
#print axioms EndgameChess.Rules.KRKSixSecond.new_geometry
#check @EndgameChess.Rules.KRKSixSecond.kernel_exact_six_iff
#print axioms EndgameChess.Rules.KRKSixSecond.kernel_exact_six_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Horizontal.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Horizontal.clear_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Horizontal.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Horizontal.history_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Vertical.clear_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Vertical.clear_append_iff
#check @EndgameChess.Rules.KRKSlotPrefix.Vertical.history_append_iff
#print axioms EndgameChess.Rules.KRKSlotPrefix.Vertical.history_append_iff
#check @EndgameChess.Rules.KRKStrongPrefix.strong_quiet
#print axioms EndgameChess.Rules.KRKStrongPrefix.strong_quiet
#check @EndgameChess.Rules.KRKStrongPrefix.occurrences_append
#print axioms EndgameChess.Rules.KRKStrongPrefix.occurrences_append
#check @EndgameChess.Rules.KRKStrongPrefix.original_entry_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.original_entry_append_iff
#check @EndgameChess.Rules.KRKStrongPrefix.clear_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.clear_append_iff
#check @EndgameChess.Rules.KRKStrongPrefix.weak_append_iff
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_append_iff
#check @EndgameChess.Rules.KRKStrongPrefix.weak_clear_kernel
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_clear_kernel
#check @EndgameChess.Rules.KRKStrongPrefix.weak_clear_ongoing
#print axioms EndgameChess.Rules.KRKStrongPrefix.weak_clear_ongoing
#check @EndgameChess.Rules.KRKTenCentralStrip.prison
#print axioms EndgameChess.Rules.KRKTenCentralStrip.prison
#check @EndgameChess.Rules.KRKTenCentralStrip.row_four_no_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.row_four_no_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.upper_no_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.upper_no_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.opposition_no_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.opposition_no_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.not_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.not_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.framed_not_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.framed_not_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.file_one_not_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.file_one_not_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.middle_not_clear
#print axioms EndgameChess.Rules.KRKTenCentralStrip.middle_not_clear
#check @EndgameChess.Rules.KRKTenCentralStrip.middle_kernel_no_ten
#print axioms EndgameChess.Rules.KRKTenCentralStrip.middle_kernel_no_ten
#check @EndgameChess.Rules.KRKTenCentralStripHolding.strong_no_twelve
#print axioms EndgameChess.Rules.KRKTenCentralStripHolding.strong_no_twelve
#check @EndgameChess.Rules.KRKTenCentralStripHolding.high_clock_holding
#print axioms EndgameChess.Rules.KRKTenCentralStripHolding.high_clock_holding
#check @EndgameChess.Rules.KRKTenEdge.nine_test_iff
#print axioms EndgameChess.Rules.KRKTenEdge.nine_test_iff
#check @EndgameChess.Rules.KRKTenEdge.clear_iff
#print axioms EndgameChess.Rules.KRKTenEdge.clear_iff
#check @EndgameChess.Rules.KRKTenEdge.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenEdge.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenGeometry.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenGeometry.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenGeometry.strong_ten_nine
#print axioms EndgameChess.Rules.KRKTenGeometry.strong_ten_nine
#check @EndgameChess.Rules.KRKTenGeometry.weak_eleven_ten
#print axioms EndgameChess.Rules.KRKTenGeometry.weak_eleven_ten
#check @EndgameChess.Rules.KRKTenGeometry.eight_region_depth
#print axioms EndgameChess.Rules.KRKTenGeometry.eight_region_depth
#check @EndgameChess.Rules.KRKTenGeometry.nine_weak_depth
#print axioms EndgameChess.Rules.KRKTenGeometry.nine_weak_depth
#check @EndgameChess.Rules.KRKTenGeometry.frame_map
#print axioms EndgameChess.Rules.KRKTenGeometry.frame_map
#check @EndgameChess.Rules.KRKTenGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKTenGlobal.edge_clear_iff
#check @EndgameChess.Rules.KRKTenGlobal.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenGlobal.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenGlobal.region_live
#print axioms EndgameChess.Rules.KRKTenGlobal.region_live
#check @EndgameChess.Rules.KRKTenGlobal.kernel_exact_ten_iff
#print axioms EndgameChess.Rules.KRKTenGlobal.kernel_exact_ten_iff
#check @EndgameChess.Rules.KRKTenInner.near_guard_necessary
#print axioms EndgameChess.Rules.KRKTenInner.near_guard_necessary
#check @EndgameChess.Rules.KRKTenInner.necessary
#print axioms EndgameChess.Rules.KRKTenInner.necessary
#check @EndgameChess.Rules.KRKTenInner.side_extra_clear
#print axioms EndgameChess.Rules.KRKTenInner.side_extra_clear
#check @EndgameChess.Rules.KRKTenInner.high_extra_clear
#print axioms EndgameChess.Rules.KRKTenInner.high_extra_clear
#check @EndgameChess.Rules.KRKTenInner.horizontal_clear
#print axioms EndgameChess.Rules.KRKTenInner.horizontal_clear
#check @EndgameChess.Rules.KRKTenInner.sufficient
#print axioms EndgameChess.Rules.KRKTenInner.sufficient
#check @EndgameChess.Rules.KRKTenInner.clear_iff
#print axioms EndgameChess.Rules.KRKTenInner.clear_iff
#check @EndgameChess.Rules.KRKTenInner.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenInner.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenInner.kernel_exact_ten
#print axioms EndgameChess.Rules.KRKTenInner.kernel_exact_ten
#check @EndgameChess.Rules.KRKTenInner.framed_clear_iff
#print axioms EndgameChess.Rules.KRKTenInner.framed_clear_iff
#check @EndgameChess.Rules.KRKTenInterior.central_escape
#print axioms EndgameChess.Rules.KRKTenInterior.central_escape
#check @EndgameChess.Rules.KRKTenInterior.deep_not_clear
#print axioms EndgameChess.Rules.KRKTenInterior.deep_not_clear
#check @EndgameChess.Rules.KRKTenInterior.weak_ten_depth_le_one
#print axioms EndgameChess.Rules.KRKTenInterior.weak_ten_depth_le_one
#check @EndgameChess.Rules.KRKTenInteriorExact.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenInteriorExact.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenInteriorExact.kernel_exact_ten
#print axioms EndgameChess.Rules.KRKTenInteriorExact.kernel_exact_ten
#check @EndgameChess.Rules.KRKTenInteriorHolding.strong_twelve_depth_le_one
#print axioms EndgameChess.Rules.KRKTenInteriorHolding.strong_twelve_depth_le_one
#check @EndgameChess.Rules.KRKTenInteriorHolding.high_clock_depth_necessary
#print axioms EndgameChess.Rules.KRKTenInteriorHolding.high_clock_depth_necessary
#check @EndgameChess.Rules.KRKTenInteriorHolding.high_clock_deep_holding
#print axioms EndgameChess.Rules.KRKTenInteriorHolding.high_clock_deep_holding
#check @EndgameChess.Rules.KRKTenNearStrip.lower_neighbour_covered
#print axioms EndgameChess.Rules.KRKTenNearStrip.lower_neighbour_covered
#check @EndgameChess.Rules.KRKTenNearStrip.no_lower_guard
#print axioms EndgameChess.Rules.KRKTenNearStrip.no_lower_guard
#check @EndgameChess.Rules.KRKTenNearStrip.prison
#print axioms EndgameChess.Rules.KRKTenNearStrip.prison
#check @EndgameChess.Rules.KRKTenNearStrip.diagonal_near_eight_clear
#print axioms EndgameChess.Rules.KRKTenNearStrip.diagonal_near_eight_clear
#check @EndgameChess.Rules.KRKTenNearStrip.row_three_clear
#print axioms EndgameChess.Rules.KRKTenNearStrip.row_three_clear
#check @EndgameChess.Rules.KRKTenNearStrip.kernel_row_three_exact_ten
#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_row_three_exact_ten
#check @EndgameChess.Rules.KRKTenNearStrip.file_one_necessary
#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_necessary
#check @EndgameChess.Rules.KRKTenNearStrip.file_one_clear
#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_clear
#check @EndgameChess.Rules.KRKTenNearStrip.file_one_iff
#print axioms EndgameChess.Rules.KRKTenNearStrip.file_one_iff
#check @EndgameChess.Rules.KRKTenNearStrip.upper_necessary
#print axioms EndgameChess.Rules.KRKTenNearStrip.upper_necessary
#check @EndgameChess.Rules.KRKTenNearStrip.necessary
#print axioms EndgameChess.Rules.KRKTenNearStrip.necessary
#check @EndgameChess.Rules.KRKTenNearStrip.upper_clear
#print axioms EndgameChess.Rules.KRKTenNearStrip.upper_clear
#check @EndgameChess.Rules.KRKTenNearStrip.sufficient
#print axioms EndgameChess.Rules.KRKTenNearStrip.sufficient
#check @EndgameChess.Rules.KRKTenNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKTenNearStrip.clear_iff
#check @EndgameChess.Rules.KRKTenNearStrip.kernel_ten_iff
#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_ten_iff
#check @EndgameChess.Rules.KRKTenNearStrip.kernel_exact_ten
#print axioms EndgameChess.Rules.KRKTenNearStrip.kernel_exact_ten
#check @EndgameChess.Rules.KRKTenNearStrip.framed_clear_iff
#print axioms EndgameChess.Rules.KRKTenNearStrip.framed_clear_iff
#check @EndgameChess.Rules.KRKTenPlyExact.necessary
#print axioms EndgameChess.Rules.KRKTenPlyExact.necessary
#check @EndgameChess.Rules.KRKTenPlyExact.rule_ten_iff
#print axioms EndgameChess.Rules.KRKTenPlyExact.rule_ten_iff
#check @EndgameChess.Rules.KRKTenPlyExact.high_clock_distance_split
#print axioms EndgameChess.Rules.KRKTenPlyExact.high_clock_distance_split
#check @EndgameChess.Rules.KRKTenPlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKTenPlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKTenPlyHistory.after_weak_iff
#print axioms EndgameChess.Rules.KRKTenPlyHistory.after_weak_iff
#check @EndgameChess.Rules.KRKTenPlyHistory.child_nine_certificate
#print axioms EndgameChess.Rules.KRKTenPlyHistory.child_nine_certificate
#check @EndgameChess.Rules.KRKTenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKTenPlyHistory.necessary
#check @EndgameChess.Rules.KRKTenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKTenPlyHistory.sufficient
#check @EndgameChess.Rules.KRKTenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKTenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKTenPlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKTenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKTenPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKTenSecondCorner.bad_neighbour_covered
#print axioms EndgameChess.Rules.KRKTenSecondCorner.bad_neighbour_covered
#check @EndgameChess.Rules.KRKTenSecondCorner.prison
#print axioms EndgameChess.Rules.KRKTenSecondCorner.prison
#check @EndgameChess.Rules.KRKTenSecondCorner.horizontal_escape
#print axioms EndgameChess.Rules.KRKTenSecondCorner.horizontal_escape
#check @EndgameChess.Rules.KRKTenSecondCorner.not_clear
#print axioms EndgameChess.Rules.KRKTenSecondCorner.not_clear
#check @EndgameChess.Rules.KRKTenSecondCorner.framed_not_clear
#print axioms EndgameChess.Rules.KRKTenSecondCorner.framed_not_clear
#check @EndgameChess.Rules.KRKTenSecondCorner.kernel_no_ten
#print axioms EndgameChess.Rules.KRKTenSecondCorner.kernel_no_ten
#check @EndgameChess.Rules.KRKTenSecondCorner.framed_kernel_no_ten
#print axioms EndgameChess.Rules.KRKTenSecondCorner.framed_kernel_no_ten
#check @EndgameChess.Rules.KRKTenSecondCornerHolding.strong_no_twelve
#print axioms EndgameChess.Rules.KRKTenSecondCornerHolding.strong_no_twelve
#check @EndgameChess.Rules.KRKTenSecondCornerHolding.high_clock_holding
#print axioms EndgameChess.Rules.KRKTenSecondCornerHolding.high_clock_holding
#check @EndgameChess.Rules.KRKThirteenCentralStrip.region_shape
#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.region_shape
#check @EndgameChess.Rules.KRKThirteenCentralStrip.rook_line_necessary
#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.rook_line_necessary
#check @EndgameChess.Rules.KRKThirteenCentralStrip.rook_destination
#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.rook_destination
#check @EndgameChess.Rules.KRKThirteenCentralStrip.clear_iff
#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.clear_iff
#check @EndgameChess.Rules.KRKThirteenCentralStrip.kernel_thirteen_iff
#print axioms EndgameChess.Rules.KRKThirteenCentralStrip.kernel_thirteen_iff
#check @EndgameChess.Rules.KRKThirteenEntry.twelve_entry_move
#print axioms EndgameChess.Rules.KRKThirteenEntry.twelve_entry_move
#check @EndgameChess.Rules.KRKThirteenGeometry.entry_sufficient
#print axioms EndgameChess.Rules.KRKThirteenGeometry.entry_sufficient
#check @EndgameChess.Rules.KRKThirteenGeometry.sufficient
#print axioms EndgameChess.Rules.KRKThirteenGeometry.sufficient
#check @EndgameChess.Rules.KRKThirteenGeometry.entry_necessary
#print axioms EndgameChess.Rules.KRKThirteenGeometry.entry_necessary
#check @EndgameChess.Rules.KRKThirteenGeometry.necessary
#print axioms EndgameChess.Rules.KRKThirteenGeometry.necessary
#check @EndgameChess.Rules.KRKThirteenGeometry.kernel_thirteen_iff
#print axioms EndgameChess.Rules.KRKThirteenGeometry.kernel_thirteen_iff
#check @EndgameChess.Rules.KRKThirteenGeometry.frame_map
#print axioms EndgameChess.Rules.KRKThirteenGeometry.frame_map
#check @EndgameChess.Rules.KRKThirteenGeometry.king_step_clear
#print axioms EndgameChess.Rules.KRKThirteenGeometry.king_step_clear
#check @EndgameChess.Rules.KRKThirteenGeometry.rook_step_clear
#print axioms EndgameChess.Rules.KRKThirteenGeometry.rook_step_clear
#check @EndgameChess.Rules.KRKThirteenInnerRook.high_destination
#print axioms EndgameChess.Rules.KRKThirteenInnerRook.high_destination
#check @EndgameChess.Rules.KRKThirteenInnerRook.rook_line_necessary
#print axioms EndgameChess.Rules.KRKThirteenInnerRook.rook_line_necessary
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.second_region_iff
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.second_region_iff
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.near_region_iff
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.near_region_iff
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.central_region_iff
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.central_region_iff
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.second_entry_necessary
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.second_entry_necessary
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.central_four_four_no_thirteen
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.central_four_four_no_thirteen
#check @EndgameChess.Rules.KRKThirteenInteriorBarriers.near_upper_no_thirteen
#print axioms EndgameChess.Rules.KRKThirteenInteriorBarriers.near_upper_no_thirteen
#check @EndgameChess.Rules.KRKThirteenNearRook.rook_line_necessary
#print axioms EndgameChess.Rules.KRKThirteenNearRook.rook_line_necessary
#check @EndgameChess.Rules.KRKThirteenNearRook.rook_destination
#print axioms EndgameChess.Rules.KRKThirteenNearRook.rook_destination
#check @EndgameChess.Rules.KRKThirteenNearStrip.region_shape
#print axioms EndgameChess.Rules.KRKThirteenNearStrip.region_shape
#check @EndgameChess.Rules.KRKThirteenNearStrip.clear_iff
#print axioms EndgameChess.Rules.KRKThirteenNearStrip.clear_iff
#check @EndgameChess.Rules.KRKThirteenNearStrip.kernel_thirteen_iff
#print axioms EndgameChess.Rules.KRKThirteenNearStrip.kernel_thirteen_iff
#check @EndgameChess.Rules.KRKThirteenNearStrip.kernel_exact_thirteen
#print axioms EndgameChess.Rules.KRKThirteenNearStrip.kernel_exact_thirteen
#check @EndgameChess.Rules.KRKThirteenPlyExact.necessary
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.necessary
#check @EndgameChess.Rules.KRKThirteenPlyExact.rule_thirteen_iff
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.rule_thirteen_iff
#check @EndgameChess.Rules.KRKThirteenPlyExact.strong_fourteen_thirteen
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.strong_fourteen_thirteen
#check @EndgameChess.Rules.KRKThirteenPlyExact.weak_fifteen_fourteen
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.weak_fifteen_fourteen
#check @EndgameChess.Rules.KRKThirteenPlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.distance_cases
#check @EndgameChess.Rules.KRKThirteenPlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKThirteenPlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKThirteenPlyHistory.clear_geometry
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.clear_geometry
#check @EndgameChess.Rules.KRKThirteenPlyHistory.clear_kernel
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.clear_kernel
#check @EndgameChess.Rules.KRKThirteenPlyHistory.entry_certificate
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.entry_certificate
#check @EndgameChess.Rules.KRKThirteenPlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.sufficient
#check @EndgameChess.Rules.KRKThirteenPlyHistory.necessary
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.necessary
#check @EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKThirteenPlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKThirteenSlots.region_point
#print axioms EndgameChess.Rules.KRKThirteenSlots.region_point
#check @EndgameChess.Rules.KRKThreePly.castle_not_last
#print axioms EndgameChess.Rules.KRKThreePly.castle_not_last
#check @EndgameChess.Rules.KRKThreePly.king_move_model
#print axioms EndgameChess.Rules.KRKThreePly.king_move_model
#check @EndgameChess.Rules.KRKThreePly.last_entry_move
#print axioms EndgameChess.Rules.KRKThreePly.last_entry_move
#check @EndgameChess.Rules.KRKThreePly.rook_entry_legal
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_legal
#check @EndgameChess.Rules.KRKThreePly.king_entry_legal
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_legal
#check @EndgameChess.Rules.KRKThreePly.strong_three_iff
#print axioms EndgameChess.Rules.KRKThreePly.strong_three_iff
#check @EndgameChess.Rules.KRKThreePly.last_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.last_corner_iff
#check @EndgameChess.Rules.KRKThreePly.immediate_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_corner_iff
#check @EndgameChess.Rules.KRKThreePly.king_entry_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_corner_iff
#check @EndgameChess.Rules.KRKThreePly.rook_entry_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_corner_iff
#check @EndgameChess.Rules.KRKThreePly.three_corner_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_corner_iff
#check @EndgameChess.Rules.KRKThreePlyExact.history_three_iff
#print axioms EndgameChess.Rules.KRKThreePlyExact.history_three_iff
#check @EndgameChess.Rules.KRKThreePlyExact.global_three_iff
#print axioms EndgameChess.Rules.KRKThreePlyExact.global_three_iff
#check @EndgameChess.Rules.KRKThreePlyExact.not_immediate_not_two
#print axioms EndgameChess.Rules.KRKThreePlyExact.not_immediate_not_two
#check @EndgameChess.Rules.KRKThreePly.entry_no_claim_iff
#print axioms EndgameChess.Rules.KRKThreePly.entry_no_claim_iff
#check @EndgameChess.Rules.KRKThreePly.canonical_king_material
#print axioms EndgameChess.Rules.KRKThreePly.canonical_king_material
#check @EndgameChess.Rules.KRKThreePly.history_three_sufficient
#print axioms EndgameChess.Rules.KRKThreePly.history_three_sufficient
#check @EndgameChess.Rules.KRKThreePly.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_force_iff
#check @EndgameChess.Rules.KRKThreePly.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_actual_iff
#check @EndgameChess.Rules.KRKThreePly.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_hold_iff
#check @EndgameChess.Rules.KRKThreePly.high_clock_exact_three
#print axioms EndgameChess.Rules.KRKThreePly.high_clock_exact_three
#check @EndgameChess.Rules.KRKThreePly.last_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.last_middle_iff
#check @EndgameChess.Rules.KRKThreePly.immediate_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_middle_iff
#check @EndgameChess.Rules.KRKThreePly.king_entry_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_middle_iff
#check @EndgameChess.Rules.KRKThreePly.rook_entry_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_middle_iff
#check @EndgameChess.Rules.KRKThreePly.three_middle_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_middle_iff
#check @EndgameChess.Rules.KRKThreePly.last_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.last_near_iff
#check @EndgameChess.Rules.KRKThreePly.immediate_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.immediate_near_iff
#check @EndgameChess.Rules.KRKThreePly.king_entry_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.king_entry_near_iff
#check @EndgameChess.Rules.KRKThreePly.rook_entry_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.rook_entry_near_iff
#check @EndgameChess.Rules.KRKThreePly.three_near_iff
#print axioms EndgameChess.Rules.KRKThreePly.three_near_iff
#check @EndgameChess.Rules.KRKTwelveCentralEntries.near_eight_region
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.near_eight_region
#check @EndgameChess.Rules.KRKTwelveCentralEntries.near_nine_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.near_nine_clear
#check @EndgameChess.Rules.KRKTwelveCentralEntries.middle_ten_region
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_ten_region
#check @EndgameChess.Rules.KRKTwelveCentralEntries.middle_eight_region
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_eight_region
#check @EndgameChess.Rules.KRKTwelveCentralEntries.middle_nine_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.middle_nine_clear
#check @EndgameChess.Rules.KRKTwelveCentralEntries.second_ten_region
#print axioms EndgameChess.Rules.KRKTwelveCentralEntries.second_ten_region
#check @EndgameChess.Rules.KRKTwelveCentralExact.opposition_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.opposition_clear
#check @EndgameChess.Rules.KRKTwelveCentralExact.necessary
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.necessary
#check @EndgameChess.Rules.KRKTwelveCentralExact.sufficient
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.sufficient
#check @EndgameChess.Rules.KRKTwelveCentralExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveCentralExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveCentralExact.framed_clear_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralExact.framed_clear_iff
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eight
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eight
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_ten
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_ten
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_eleven
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.second_eleven
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_ten
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_ten
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eleven
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.middle_eleven
#check @EndgameChess.Rules.KRKTwelveCentralOppositionEntries.high_eleven
#print axioms EndgameChess.Rules.KRKTwelveCentralOppositionEntries.high_eleven
#check @EndgameChess.Rules.KRKTwelveCentralStrip.prison
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.prison
#check @EndgameChess.Rules.KRKTwelveCentralStrip.row_four_necessary
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.row_four_necessary
#check @EndgameChess.Rules.KRKTwelveCentralStrip.upper_necessary
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.upper_necessary
#check @EndgameChess.Rules.KRKTwelveCentralStrip.protected_two_four_no_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.protected_two_four_no_clear
#check @EndgameChess.Rules.KRKTwelveCentralStrip.candidate_necessary
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.candidate_necessary
#check @EndgameChess.Rules.KRKTwelveCentralStrip.row_four_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.row_four_clear
#check @EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_iff
#check @EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveCentralStrip.kernel_row_four_exact_twelve
#check @EndgameChess.Rules.KRKTwelveCentralUpper.upper_two_no_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_two_no_clear
#check @EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_high_no_clear
#check @EndgameChess.Rules.KRKTwelveCentralUpper.protected_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.protected_clear
#check @EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_one_iff
#check @EndgameChess.Rules.KRKTwelveCentralUpper.upper_zero_no_clear
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_zero_no_clear
#check @EndgameChess.Rules.KRKTwelveCentralUpper.upper_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.upper_iff
#check @EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_iff
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_iff
#check @EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveCentralUpper.kernel_upper_exact_twelve
#check @EndgameChess.Rules.KRKTwelveCentralUpperEntries.near_eight
#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.near_eight
#check @EndgameChess.Rules.KRKTwelveCentralUpperEntries.middle_eight
#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.middle_eight
#check @EndgameChess.Rules.KRKTwelveCentralUpperEntries.second_eight
#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.second_eight
#check @EndgameChess.Rules.KRKTwelveCentralUpperEntries.ten_edge_region
#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.ten_edge_region
#check @EndgameChess.Rules.KRKTwelveCentralUpperEntries.edge_eleven
#print axioms EndgameChess.Rules.KRKTwelveCentralUpperEntries.edge_eleven
#check @EndgameChess.Rules.KRKTwelveDeepExact.central_escape
#print axioms EndgameChess.Rules.KRKTwelveDeepExact.central_escape
#check @EndgameChess.Rules.KRKTwelveDeepExact.corner_target
#print axioms EndgameChess.Rules.KRKTwelveDeepExact.corner_target
#check @EndgameChess.Rules.KRKTwelveDeepExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveDeepExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveDeepExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveDeepExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveEdge.eleven_test_iff
#print axioms EndgameChess.Rules.KRKTwelveEdge.eleven_test_iff
#check @EndgameChess.Rules.KRKTwelveEdge.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveEdge.clear_iff
#check @EndgameChess.Rules.KRKTwelveEdge.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveEdge.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveGeometry.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveGeometry.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveGeometry.strong_twelve_eleven
#print axioms EndgameChess.Rules.KRKTwelveGeometry.strong_twelve_eleven
#check @EndgameChess.Rules.KRKTwelveGeometry.weak_thirteen_twelve
#print axioms EndgameChess.Rules.KRKTwelveGeometry.weak_thirteen_twelve
#check @EndgameChess.Rules.KRKTwelveGeometry.ten_region_depth
#print axioms EndgameChess.Rules.KRKTwelveGeometry.ten_region_depth
#check @EndgameChess.Rules.KRKTwelveGeometry.eleven_weak_depth
#print axioms EndgameChess.Rules.KRKTwelveGeometry.eleven_weak_depth
#check @EndgameChess.Rules.KRKTwelveGeometry.frame_map
#print axioms EndgameChess.Rules.KRKTwelveGeometry.frame_map
#check @EndgameChess.Rules.KRKTwelveGlobal.edge_clear_iff
#print axioms EndgameChess.Rules.KRKTwelveGlobal.edge_clear_iff
#check @EndgameChess.Rules.KRKTwelveGlobal.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveGlobal.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveGlobal.region_live
#print axioms EndgameChess.Rules.KRKTwelveGlobal.region_live
#check @EndgameChess.Rules.KRKTwelveGlobal.kernel_exact_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveGlobal.kernel_exact_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInner.near_guard_prison
#print axioms EndgameChess.Rules.KRKTwelveInner.near_guard_prison
#check @EndgameChess.Rules.KRKTwelveInner.prison
#print axioms EndgameChess.Rules.KRKTwelveInner.prison
#check @EndgameChess.Rules.KRKTwelveInner.same_file_rook_below
#print axioms EndgameChess.Rules.KRKTwelveInner.same_file_rook_below
#check @EndgameChess.Rules.KRKTwelveInner.zero_five_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInner.zero_five_high_no_clear
#check @EndgameChess.Rules.KRKTwelveInner.one_five_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInner.one_five_high_no_clear
#check @EndgameChess.Rules.KRKTwelveInner.near_guard_sharp
#print axioms EndgameChess.Rules.KRKTwelveInner.near_guard_sharp
#check @EndgameChess.Rules.KRKTwelveInner.ten_clear_subset
#print axioms EndgameChess.Rules.KRKTwelveInner.ten_clear_subset
#check @EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.low_second
#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.low_second
#check @EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_second
#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_second
#check @EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_near
#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_near
#check @EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerBoundaryEntries.protected_clear
#check @EndgameChess.Rules.KRKTwelveInnerDiagonal.clear
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.clear
#check @EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_twelve
#check @EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonal.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerDiagonalExact.necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.necessary
#check @EndgameChess.Rules.KRKTwelveInnerDiagonalExact.sufficient
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.sufficient
#check @EndgameChess.Rules.KRKTwelveInnerDiagonalExact.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerDiagonalExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerExact.necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.necessary
#check @EndgameChess.Rules.KRKTwelveInnerExact.sufficient
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.sufficient
#check @EndgameChess.Rules.KRKTwelveInnerExact.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInnerExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerExact.framed_clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerExact.framed_clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.high_no_clear
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.five_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.five_clear
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_height_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerFileOne.kernel_height_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerHigh.clear
#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.clear
#check @EndgameChess.Rules.KRKTwelveInnerHigh.kernel_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.kernel_twelve
#check @EndgameChess.Rules.KRKTwelveInnerHigh.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerHigh.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerHighExact.necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.necessary
#check @EndgameChess.Rules.KRKTwelveInnerHighExact.sufficient
#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.sufficient
#check @EndgameChess.Rules.KRKTwelveInnerHighExact.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerHighExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerOuter.high_second_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_second_ten
#check @EndgameChess.Rules.KRKTwelveInnerOuter.high_corner_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_corner_ten
#check @EndgameChess.Rules.KRKTwelveInnerOuter.low_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.low_clear
#check @EndgameChess.Rules.KRKTwelveInnerOuter.high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.high_no_clear
#check @EndgameChess.Rules.KRKTwelveInnerOuter.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerOuter.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerOuter.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerSide.necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerSide.necessary
#check @EndgameChess.Rules.KRKTwelveInnerSide.sufficient
#print axioms EndgameChess.Rules.KRKTwelveInnerSide.sufficient
#check @EndgameChess.Rules.KRKTwelveInnerSide.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerSide.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerSide.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerSide.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInnerSide.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerSide.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerUpperBoundary.upper_three_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.upper_three_no_clear
#check @EndgameChess.Rules.KRKTwelveInnerUpperBoundary.two_five_four_no_clear
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.two_five_four_no_clear
#check @EndgameChess.Rules.KRKTwelveInnerUpperBoundary.five_necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperBoundary.five_necessary
#check @EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_eight
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_eight
#check @EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.low_near_ten
#check @EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_corner_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_corner_ten
#check @EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_near_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.upper_near_ten
#check @EndgameChess.Rules.KRKTwelveInnerUpperEntries.second_outer_ten
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperEntries.second_outer_ten
#check @EndgameChess.Rules.KRKTwelveInnerUpperFive.clear
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.clear
#check @EndgameChess.Rules.KRKTwelveInnerUpperFive.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerUpperFive.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFive.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInnerUpperFour.necessary
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.necessary
#check @EndgameChess.Rules.KRKTwelveInnerUpperFour.sufficient
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.sufficient
#check @EndgameChess.Rules.KRKTwelveInnerUpperFour.clear_iff
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.clear_iff
#check @EndgameChess.Rules.KRKTwelveInnerUpperFour.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInnerUpperFour.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveInteriorExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveInteriorExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveInteriorExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveInteriorExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveNearExact.row_two_clear
#print axioms EndgameChess.Rules.KRKTwelveNearExact.row_two_clear
#check @EndgameChess.Rules.KRKTwelveNearExact.necessary
#print axioms EndgameChess.Rules.KRKTwelveNearExact.necessary
#check @EndgameChess.Rules.KRKTwelveNearExact.sufficient
#print axioms EndgameChess.Rules.KRKTwelveNearExact.sufficient
#check @EndgameChess.Rules.KRKTwelveNearExact.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve_iff
#check @EndgameChess.Rules.KRKTwelveNearExact.fresh_iff
#print axioms EndgameChess.Rules.KRKTwelveNearExact.fresh_iff
#check @EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveNearExact.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveNearExact.framed_clear_iff
#print axioms EndgameChess.Rules.KRKTwelveNearExact.framed_clear_iff
#check @EndgameChess.Rules.KRKTwelveNearFileEntries.eight_region_subset
#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.eight_region_subset
#check @EndgameChess.Rules.KRKTwelveNearFileEntries.low_ten
#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.low_ten
#check @EndgameChess.Rules.KRKTwelveNearFileEntries.low_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.low_eleven
#check @EndgameChess.Rules.KRKTwelveNearFileEntries.middle_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearFileEntries.middle_eleven
#check @EndgameChess.Rules.KRKTwelveNearFileOne.high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.high_no_clear
#check @EndgameChess.Rules.KRKTwelveNearFileOne.necessary
#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.necessary
#check @EndgameChess.Rules.KRKTwelveNearFileOne.sufficient
#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.sufficient
#check @EndgameChess.Rules.KRKTwelveNearFileOne.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveNearFileOne.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveNearFileOne.kernel_exact_twelve
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.low_near_ten
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.low_near_ten
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.upper_second_ten
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_second_ten
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.high_near_ten
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.high_near_ten
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.upper_low_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_low_eleven
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.row_near_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_near_eleven
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.row_middle_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_middle_eleven
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.row_lower_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_lower_eleven
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.row_inner_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.row_inner_eleven
#check @EndgameChess.Rules.KRKTwelveNearNewEntries.upper_inner_eleven
#print axioms EndgameChess.Rules.KRKTwelveNearNewEntries.upper_inner_eleven
#check @EndgameChess.Rules.KRKTwelveNearStrip.prison
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.prison
#check @EndgameChess.Rules.KRKTwelveNearStrip.row_two_necessary
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_two_necessary
#check @EndgameChess.Rules.KRKTwelveNearStrip.protected_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.protected_high_no_clear
#check @EndgameChess.Rules.KRKTwelveNearStrip.row_three_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_three_high_no_clear
#check @EndgameChess.Rules.KRKTwelveNearStrip.row_three_necessary
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.row_three_necessary
#check @EndgameChess.Rules.KRKTwelveNearStrip.upper_low_no_clear
#print axioms EndgameChess.Rules.KRKTwelveNearStrip.upper_low_no_clear
#check @EndgameChess.Rules.KRKTwelveNearUpper.blocked_high_no_clear
#print axioms EndgameChess.Rules.KRKTwelveNearUpper.blocked_high_no_clear
#check @EndgameChess.Rules.KRKTwelveNearUpper.necessary
#print axioms EndgameChess.Rules.KRKTwelveNearUpper.necessary
#check @EndgameChess.Rules.KRKTwelveNearUpper.ten_clear_subset
#print axioms EndgameChess.Rules.KRKTwelveNearUpper.ten_clear_subset
#check @EndgameChess.Rules.KRKTwelveNearUpper.protected_clear
#print axioms EndgameChess.Rules.KRKTwelveNearUpper.protected_clear
#check @EndgameChess.Rules.KRKTwelveNearUpper.sufficient
#print axioms EndgameChess.Rules.KRKTwelveNearUpper.sufficient
#check @EndgameChess.Rules.KRKTwelvePlyExact.necessary
#print axioms EndgameChess.Rules.KRKTwelvePlyExact.necessary
#check @EndgameChess.Rules.KRKTwelvePlyExact.rule_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyExact.rule_twelve_iff
#check @EndgameChess.Rules.KRKTwelvePlyExact.distance_cases
#print axioms EndgameChess.Rules.KRKTwelvePlyExact.distance_cases
#check @EndgameChess.Rules.KRKTwelvePlyExact.high_clock_exact_distance
#print axioms EndgameChess.Rules.KRKTwelvePlyExact.high_clock_exact_distance
#check @EndgameChess.Rules.KRKTwelvePlyHistory.after_weak_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.after_weak_iff
#check @EndgameChess.Rules.KRKTwelvePlyHistory.child_eleven_certificate
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.child_eleven_certificate
#check @EndgameChess.Rules.KRKTwelvePlyHistory.necessary
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.necessary
#check @EndgameChess.Rules.KRKTwelvePlyHistory.sufficient
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.sufficient
#check @EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_force_iff
#check @EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_actual_iff
#check @EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_hold_iff
#check @EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_draw_iff
#print axioms EndgameChess.Rules.KRKTwelvePlyHistory.high_clock_draw_iff
#check @EndgameChess.Rules.KRKTwelveSecondCorner.bad_neighbour_covered
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.bad_neighbour_covered
#check @EndgameChess.Rules.KRKTwelveSecondCorner.prison
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.prison
#check @EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_necessary
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_necessary
#check @EndgameChess.Rules.KRKTwelveSecondCorner.necessary
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.necessary
#check @EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_clear
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.horizontal_clear
#check @EndgameChess.Rules.KRKTwelveSecondCorner.sufficient
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.sufficient
#check @EndgameChess.Rules.KRKTwelveSecondCorner.kernel_twelve_iff
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.kernel_twelve_iff
#check @EndgameChess.Rules.KRKTwelveSecondCorner.kernel_exact_twelve
#print axioms EndgameChess.Rules.KRKTwelveSecondCorner.kernel_exact_twelve
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_swap_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_swap_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_vertical_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_vertical_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.immediate_vertical_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.immediate_vertical_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_geometry
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_geometry
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_reply_distance
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_reply_distance
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_slots_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.last_slots_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.file_return_legal
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.file_return_legal
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_sees_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.slot_sees_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.king_history_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.king_history_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.rook_history_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.rook_history_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_force_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_force_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_actual_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_actual_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_hold_iff
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_hold_iff
#check @EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_distance_cases
#print axioms EndgameChess.Rules.KRKVerticalNearSlotBarriers.high_clock_distance_cases
#check @EndgameChess.Rules.KRKWeakBranch.history_geometry
#print axioms EndgameChess.Rules.KRKWeakBranch.history_geometry
#check @EndgameChess.Rules.KRKWeakBranch.child_clock
#print axioms EndgameChess.Rules.KRKWeakBranch.child_clock
#check @EndgameChess.Rules.KRKWeakBranch.child_ongoing_of_force
#print axioms EndgameChess.Rules.KRKWeakBranch.child_ongoing_of_force
#check @EndgameChess.Rules.KRKWeakBranch.child_history_of_force
#print axioms EndgameChess.Rules.KRKWeakBranch.child_history_of_force
#check @EndgameChess.Rules.KRKWeakBranch.child_certificate
#print axioms EndgameChess.Rules.KRKWeakBranch.child_certificate
#check @EndgameChess.Rules.KRKWeakBranch.admitted_far
#print axioms EndgameChess.Rules.KRKWeakBranch.admitted_far
#check @EndgameChess.Rules.KRKWeakBranch.weak_not_one
#print axioms EndgameChess.Rules.KRKWeakBranch.weak_not_one
#check @EndgameChess.Rules.KRKWeakPrefixEntry.entry_queries_unchanged
#print axioms EndgameChess.Rules.KRKWeakPrefixEntry.entry_queries_unchanged
#check @EndgameChess.Rules.KRKWeakPrefixEntry.entry_append_iff
#print axioms EndgameChess.Rules.KRKWeakPrefixEntry.entry_append_iff
