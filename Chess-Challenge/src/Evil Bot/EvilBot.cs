using ChessChallenge.API;
using System;
using System.Numerics;

namespace ChessChallenge.Example {
  public class EvilBot : IChessBot {
    struct TTEntry {
      public ulong key;
      public int score;
      public int depth;
      public Move bestMove;

      public TTEntry(ulong _key, int _score, int _depth, Move _bestMove) {
        key = _key;
        score = _score;
        depth = _depth;
        bestMove = _bestMove;
      }
    }

    int[] pieceScores = { 0, 115, 305, 320, 500, 910, 20000 };
    Board _board;
    const ulong entries = (1 << 19) - 1;
    TTEntry[] table = new TTEntry[entries];
    const int killerMoveMaxSize = 200;
    Move[] killerMoves = new Move[killerMoveMaxSize];
    Move _bestMove;
    int maxNum = 300000;
    Timer _timer;

    public int Evaluate() {
      int score = 0, bishopPairs = 0;

      foreach (bool stm in new[] { true, false }) {
        for (var p = PieceType.Pawn; p <= PieceType.King; p++) {
          int piece = (int)p, ind;
          ulong mask = _board.GetPieceBitboard(p, stm);
          while (mask != 0) {
            score += pieceScores[piece];
            ulong moveBitboard = 0ul;
            ind = BitboardHelper.ClearAndGetIndexOfLSB(ref mask);
            Square square = new(ind);
            switch (p) {
              case PieceType.Pawn:
                moveBitboard = BitboardHelper.GetPawnAttacks(square, stm);
                ulong squareInFront = (ulong)(1 << (ind + (stm ? 8 : -8))) & (_board.AllPiecesBitboard);
                moveBitboard |= squareInFront;
                break;
              case PieceType.King:
                break;
              case PieceType.Knight:
                moveBitboard = BitboardHelper.GetKnightAttacks(square);
                ulong enemyPawnBitboard = _board.GetPieceBitboard(PieceType.Pawn, !stm);
                while (enemyPawnBitboard != 0)
                  moveBitboard &= ~BitboardHelper.GetPawnAttacks(new Square(BitboardHelper.ClearAndGetIndexOfLSB(ref enemyPawnBitboard)), !stm);
                break;
              case PieceType.Bishop:
                bishopPairs += stm ? 2 : 5;
                goto default;
              case PieceType.Rook:
              case PieceType.Queen:
              default:
                moveBitboard = BitboardHelper.GetSliderAttacks(p, square, _board);
                break;
            }
            score += BitOperations.PopCount(moveBitboard) * 10;
          }
        }

        score = -score;
      }

      // White Pair
      if (bishopPairs % 5 == 4)
        score += 50;
      // Black Pair
      if (bishopPairs >= 10)
        score -= 50;

      return score * (_board.IsWhiteToMove ? 1 : -1);
    }

    int SearchFunction(int searchDepth, int colour, int movesMade, int alpha, int beta) {
      if (movesMade > 0 && _board.IsRepeatedPosition())
        return 0;
      ulong key = _board.ZobristKey;
      TTEntry entry = table[key % entries];
      int Big_Delta = (pieceScores[5] * 2) - pieceScores[1]; // promote to a queen, whilst taking a queen

      var legalMoves = _board.GetLegalMoves(searchDepth <= 0);

      if (searchDepth > 0 && legalMoves.Length == 0)
        return _board.IsInCheck() ? -maxNum + movesMade : 0;

      if (entry.key == key && entry.depth >= searchDepth && movesMade > 0)
        return entry.score;

      // <reverse futility pruning />
      int eval;
      if (entry.key == key)
        eval = entry.score;
      else
        eval = Evaluate();

      if (eval - Big_Delta >= beta)
        return eval;

      // <quiescence search>
      if (searchDepth <= 0) {

        if (eval >= beta || eval < alpha - Big_Delta)
          return eval;

        if (alpha < eval)
          alpha = eval;
      }
      // </quiescence search>

      // <null move pruning>

      if (movesMade >= 4) {
        if (_board.TrySkipTurn()) {
          eval = -SearchFunction(searchDepth - 3, -colour, movesMade + 1, -beta, -alpha);
          _board.UndoSkipTurn();
          if (eval >= beta)
            return eval;
        }
      }

      // </null move pruning>

      // <rank moves>

      Move bestMove = entry.key == key ? entry.bestMove : Move.NullMove;
      var moveScores = new int[legalMoves.Length];
      for (int i = 0; i < legalMoves.Length; i++) {
        // <hash Move />
        if (legalMoves[i] == bestMove)
          moveScores[i] = 100000;
        // <mvv-lva />
        else if (legalMoves[i].IsCapture)
          moveScores[i] = (10 * pieceScores[(int)legalMoves[i].CapturePieceType]) - pieceScores[(int)legalMoves[i].MovePieceType];
        // <killer moves />
        else if (killerMoves[movesMade % killerMoveMaxSize] == legalMoves[i])
          moveScores[i] = 10;
        // <default value />
        else
          moveScores[i] = 0;
      }

      // </rank moves>

      // <tree search>
      bestMove = legalMoves.Length > 0 ? legalMoves[0] : Move.NullMove;
      for (int i = 0; i < legalMoves.Length; i++) {
        // <sort moves>
        for (int j = i + 1; j < legalMoves.Length; j++) {
          if (moveScores[j] > moveScores[i])
            (moveScores[i], moveScores[j], legalMoves[i], legalMoves[j]) = (moveScores[j], moveScores[i], legalMoves[j], legalMoves[i]);
        }
        // </sort moves>

        if (_timer.MillisecondsElapsedThisTurn > _timer.MillisecondsRemaining / 30)
          return -maxNum;

        Move legalMove = legalMoves[i];
        _board.MakeMove(legalMove);
        // <late move reduction />
        if (moveScores[i] <= 10 && searchDepth >= 3) {
          eval = -SearchFunction(searchDepth - 3, -colour, movesMade + 1, -beta, -alpha);
          if (eval > alpha)
            eval = -SearchFunction(searchDepth - 1, -colour, movesMade + 1, -beta, -alpha);
        } else
          eval = -SearchFunction(searchDepth - 1, -colour, movesMade + 1, -beta, -alpha);
        _board.UndoMove(legalMove);
        // Fail high and add to killer move array
        if (eval >= beta) {
          killerMoves[movesMade % killerMoveMaxSize] = legalMove;
          return eval;
        }
        if (eval > alpha) {
          bestMove = legalMove;
          alpha = eval;
          if (movesMade == 0)
            _bestMove = bestMove;
        }
      }
      // </tree search>

      table[key % entries] = new TTEntry(key, alpha, searchDepth, bestMove);

      return alpha;
    }

    public Move Think(Board board, Timer timer) {
      _board = board;
      _timer = timer;
      _bestMove = Move.NullMove;
      int colour = board.IsWhiteToMove ? 1 : -1;
      sbyte depth = 1;
      while (timer.MillisecondsElapsedThisTurn < timer.MillisecondsRemaining / 30) {
        SearchFunction(depth, colour, 0, -maxNum, maxNum);
        ++depth;
      }
      return _bestMove == Move.NullMove ? _board.GetLegalMoves()[0] : _bestMove;
    }
  }
}