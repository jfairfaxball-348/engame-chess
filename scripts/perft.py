#!/usr/bin/env python3
"""Independent perft counter for the EC-C004 rules kernel (S007).

CROSS-CHECK ONLY, NOT A PROOF. Written from the FIDE 2023 Article 3 text,
independently of formal/EndgameChess/Rules/*.lean. It uses a different
representation (a 10x12 mailbox with sentinels, make/copy rather than functions)
so that the two implementations share no code or data layout.

The public reference values from the initial position are perft(1..3) = 20, 400 and
8902. These are elementary combinatorial facts about the rules, not endgame data.
"""
import sys

EMPTY, OFF = ".", "#"
# 10x12 mailbox: index = 21 + file + 10*rank, files a..h = 0..7, ranks 1..8 = 0..7.
N_, S_, E_, W_ = 10, -10, 1, -1
KNIGHT = (21, 19, 12, 8, -21, -19, -12, -8)
KING = (N_, S_, E_, W_, 11, 9, -9, -11)
DIAG = (11, 9, -9, -11)
ORTH = (N_, S_, E_, W_)


def idx(f, r):
    return 21 + f + 10 * r


def start():
    b = [OFF] * 120
    for r in range(8):
        for f in range(8):
            b[idx(f, r)] = EMPTY
    back = "RNBQKBNR"
    for f in range(8):
        b[idx(f, 0)] = back[f]
        b[idx(f, 1)] = "P"
        b[idx(f, 6)] = "p"
        b[idx(f, 7)] = back[f].lower()
    # state: board, white_to_move, castling set, ep index or None
    return (b, True, frozenset("KQkq"), None)


def own(piece, white):
    return piece not in (EMPTY, OFF) and piece.isupper() == white


def attacked(b, sq, by_white):
    """Is square `sq` attacked by a piece of the side `by_white`? (Art. 3.1.2)"""
    pawn = "P" if by_white else "p"
    d = -10 if by_white else 10  # a white pawn attacks sq from below
    for o in (d - 1, d + 1):
        if b[sq + o] == pawn:
            return True
    kn = "N" if by_white else "n"
    if any(b[sq + o] == kn for o in KNIGHT):
        return True
    kg = "K" if by_white else "k"
    if any(b[sq + o] == kg for o in KING):
        return True
    for dirs, sliders in ((DIAG, "BQ"), (ORTH, "RQ")):
        sl = sliders if by_white else sliders.lower()
        for o in dirs:
            t = sq + o
            while b[t] == EMPTY:
                t += o
            if b[t] in sl:
                return True
    return False


def king_sq(b, white):
    k = "K" if white else "k"
    return b.index(k)


def moves(state):
    b, white, cr, ep = state
    out = []
    fwd = 10 if white else -10
    start_rank = 1 if white else 6
    last_rank = 7 if white else 0
    for s in range(120):
        p = b[s]
        if not own(p, white):
            continue
        u = p.upper()
        targets = []
        if u == "P":
            t = s + fwd
            if b[t] == EMPTY:
                targets.append((t, None))
                if (s - 21) // 10 == start_rank and b[t + fwd] == EMPTY:
                    targets.append((t + fwd, "double"))
            for o in (fwd - 1, fwd + 1):
                t = s + o
                if b[t] not in (EMPTY, OFF) and not own(b[t], white) and b[t].upper() != "K":
                    targets.append((t, None))
                elif t == ep:
                    targets.append((t, "ep"))
            expanded = []
            for t, tag in targets:
                if (t - 21) // 10 == last_rank:
                    expanded += [(t, "promo" + q) for q in "QRBN"]
                else:
                    expanded.append((t, tag))
            targets = expanded
        elif u in "NK":
            for o in (KNIGHT if u == "N" else KING):
                t = s + o
                if b[t] != OFF and not own(b[t], white) and b[t].upper() != "K":
                    targets.append((t, None))
            if u == "K":
                r = 0 if white else 7
                e = idx(4, r)
                if s == e:
                    for side, rook_f, empties, safe in (("K", 7, (5, 6), (4, 5, 6)),
                                                        ("Q", 0, (1, 2, 3), (4, 3, 2))):
                        right = side if white else side.lower()
                        rook = "R" if white else "r"
                        if (right in cr and b[idx(rook_f, r)] == rook
                                and all(b[idx(f, r)] == EMPTY for f in empties)
                                and not any(attacked(b, idx(f, r), not white) for f in safe)):
                            targets.append((idx(6 if side == "K" else 2, r), "castle" + side))
        else:
            dirs = {"B": DIAG, "R": ORTH, "Q": DIAG + ORTH}[u]
            for o in dirs:
                t = s + o
                while b[t] == EMPTY:
                    targets.append((t, None))
                    t += o
                if b[t] != OFF and not own(b[t], white) and b[t].upper() != "K":
                    targets.append((t, None))
        for t, tag in targets:
            nb = b[:]
            nb[t] = nb[s]
            nb[s] = EMPTY
            nep = None
            if tag == "ep":
                nb[t - fwd] = EMPTY
            elif tag == "double":
                nep = s + fwd
            elif tag and tag.startswith("promo"):
                q = tag[-1]
                nb[t] = q if white else q.lower()
            elif tag and tag.startswith("castle"):
                r = 0 if white else 7
                if tag[-1] == "K":
                    nb[idx(5, r)], nb[idx(7, r)] = nb[idx(7, r)], EMPTY
                else:
                    nb[idx(3, r)], nb[idx(0, r)] = nb[idx(0, r)], EMPTY
            if attacked(nb, king_sq(nb, white), not white):
                continue  # Art. 3.9.2
            ncr = set(cr)
            if u == "K":
                ncr -= ({"K", "Q"} if white else {"k", "q"})
            for sq_, right in ((idx(7, 0), "K"), (idx(0, 0), "Q"), (idx(7, 7), "k"), (idx(0, 7), "q")):
                if s == sq_ or t == sq_:
                    ncr.discard(right)
            out.append((nb, not white, frozenset(ncr), nep))
    return out


def perft(state, depth):
    if depth == 0:
        return 1
    return sum(perft(s, depth - 1) for s in moves(state))


def from_fen(fen):
    """Parse the first four FEN fields: placement, side, castling, en-passant target."""
    place, side, castle, ep = fen.split()[:4]
    b = [OFF] * 120
    for r in range(8):
        for f in range(8):
            b[idx(f, r)] = EMPTY
    for i, row in enumerate(place.split("/")):
        r, f = 7 - i, 0
        for ch in row:
            if ch.isdigit():
                f += int(ch)
            else:
                b[idx(f, r)] = ch
                f += 1
    epi = None if ep == "-" else idx("abcdefgh".index(ep[0]), int(ep[1]) - 1)
    return (b, side == "w", frozenset("" if castle == "-" else castle), epi)


REFERENCE = {1: 20, 2: 400, 3: 8902}

# Published perft values (Chess Programming Wiki, "Perft Results"). These positions
# exercise castling, en passant (including en-passant pins), promotion and checks.
TEST_POSITIONS = {
    "kiwipete": ("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -",
                 [48, 2039, 97862]),
    "position3": ("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - -", [14, 191, 2812, 43238]),
    "position4": ("r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq -",
                  [6, 264, 9467]),
    "position5": ("rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ -", [44, 1486, 62379]),
}


def main(argv):
    depth = int(argv[1]) if len(argv) > 1 else 3
    ok = True
    for name, (fen, refs) in TEST_POSITIONS.items():
        for d, ref in enumerate(refs, start=1):
            n = perft(from_fen(fen), d)
            ok &= n == ref
            print(f"{name} perft({d}) = {n} {'OK' if n == ref else f'MISMATCH (expected {ref})'}")
    for d in range(1, depth + 1):
        n = perft(start(), d)
        ref = REFERENCE.get(d)
        flag = "" if ref is None else ("OK" if n == ref else f"MISMATCH (expected {ref})")
        ok &= ref is None or n == ref
        print(f"perft({d}) = {n} {flag}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
