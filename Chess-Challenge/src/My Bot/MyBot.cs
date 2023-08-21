using ChessChallenge.API;
using System;
using System.Numerics;

public class MyBot : IChessBot {
  record struct TTEntry(uint Key,
                        short Score,
                        sbyte Depth,
                        Move BestMove,
                        byte Flag);

  int[] pieceValues = { 0, 110, 307, 322, 507, 847, 0, 129, 287, 317, 457, 931, 0 }, phaseWeight = { 0, 0, 1, 1, 2, 4, 0 };
  Board globalBoard;
  int tableEntries = 0x7fffff;
  TTEntry[] transpositionTable = new TTEntry[0x800000];
  int[,,] moveHistoryTable;
  int TimeRemaining => globalTimer.MillisecondsRemaining / 50;
  int maximumScore = 30000;
  Timer globalTimer;

  public int RawEvaluation() {
    int midgameScore = 0, endgameScore = 0, phase = 0;

    foreach (bool isWhitePiece in new[] { true, false }) {
      // 1 = Pawn, 2 = Knight, 3 = Bishop, 4 = Rook, 5 = Queen, 6 = King
      for (int piece = 0; ++piece < 6;) {
        ulong mask = globalBoard.GetPieceBitboard((PieceType)piece, isWhitePiece);
        if (piece == 3 && BitOperations.PopCount(mask) > 1)
          midgameScore += 104;
        while (mask != 0) {
          Square square = new(BitboardHelper.ClearAndGetIndexOfLSB(ref mask));
          int mobilityScore = BitOperations.PopCount(BitboardHelper.GetPieceAttacks((PieceType)piece, square, globalBoard, isWhitePiece));
          midgameScore += pieceValues[piece] + mobilityScore * 11;
          endgameScore += pieceValues[piece + 6] + mobilityScore * 7;
          phase += phaseWeight[piece];
        }
      }

      midgameScore = -midgameScore;
      endgameScore = -endgameScore;
    }

    phase = Math.Min(phase, 24);

    return ((midgameScore * phase + endgameScore * (24 - phase)) / 24) * (globalBoard.IsWhiteToMove ? 1 : -1);
  }

  int SearchPosition(int searchDepth, int plyFromRoot, int alpha, int beta) {
    if (globalBoard.IsDraw())
      return 0;
    if (globalBoard.IsInCheckmate())
      return -maximumScore + plyFromRoot;
    uint key = (uint)(globalBoard.ZobristKey >> 32);
    TTEntry currentTableEntry = transpositionTable[key & tableEntries];

    bool isEntryKeyCorrect = currentTableEntry.Key == key,
      isPVNode = beta - alpha > 1,
      canReduceNode = false,
      isQuiescenceSearch = searchDepth <= 0,
      isPlayerInCheck = globalBoard.IsInCheck();
    int bestScore = -maximumScore, eval = 0, extension = isPlayerInCheck && plyFromRoot < 16 ? 1 : 0;

    int Search(int newBeta, int r = 0) => eval = -SearchPosition(searchDepth - 1 + extension - r, plyFromRoot + 1, -newBeta, -alpha);
    if (isEntryKeyCorrect && currentTableEntry.Depth >= searchDepth) {
      eval = currentTableEntry.Score;
      switch (currentTableEntry.Flag) {
        case 0:
          return eval;
        case 1:
          alpha = Math.Max(alpha, eval);
          break;
        case 2:
          beta = Math.Min(beta, eval);
          break;
      }
      if (alpha >= beta)
        return eval;
    }

    // <quiescence search>
    if (isQuiescenceSearch) {
      bestScore = RawEvaluation();
      if (bestScore >= beta)
        return bestScore;
      alpha = Math.Max(alpha, bestScore);
    }
    // </quiescence search>
    else if (!(isPVNode || isPlayerInCheck)) {
      globalBoard.TrySkipTurn();
      Search(beta, 2);
      globalBoard.UndoSkipTurn();
      if (eval >= beta)
        return eval;
      canReduceNode = searchDepth >= 3;
    }
    // <rank moves>
    Move bestMove = isEntryKeyCorrect ? currentTableEntry.BestMove : Move.NullMove, moveToEvaluate;
    Span<Move> legalMoves = stackalloc Move[256];
    globalBoard.GetLegalMovesNonAlloc(ref legalMoves, isQuiescenceSearch);
    Span<int> moveScores = stackalloc int[legalMoves.Length];
    for (int i = 0; i < legalMoves.Length; i++) {
      moveToEvaluate = legalMoves[i];
      // <hash Move />
      moveScores[i] = -(moveToEvaluate == bestMove
        ? 10000000
        : moveToEvaluate.IsCapture
        ? 1000 * pieceValues[(int)moveToEvaluate.CapturePieceType] - pieceValues[(int)moveToEvaluate.MovePieceType]
        : moveHistoryTable[plyFromRoot & 1, (int)moveToEvaluate.MovePieceType, moveToEvaluate.TargetSquare.Index]);
    }
    // </rank moves>
    moveScores.Sort(legalMoves);

    // <tree search>
    for (int movesChecked = 0; movesChecked < legalMoves.Length; movesChecked++) {

      moveToEvaluate = legalMoves[movesChecked];
      globalBoard.MakeMove(moveToEvaluate);
      // split out from the other condition to avoid doing a zero width search needlessly
      if (isQuiescenceSearch || movesChecked == 0)
        Search(beta);
      else if ((globalBoard.IsInCheck() || !canReduceNode || moveToEvaluate.IsCapture || moveToEvaluate.IsPromotion
                  ? eval = alpha + 1
                  : Search(alpha + 1, movesChecked / 7 + searchDepth / 7)) > alpha
              && alpha < Search(alpha + 1))
        Search(beta);
      globalBoard.UndoMove(moveToEvaluate);

      if (globalTimer.MillisecondsElapsedThisTurn > TimeRemaining)
        return maximumScore;

      if (eval > bestScore) {
        bestMove = moveToEvaluate;
        bestScore = eval;
        if (eval >= beta) {
          if (!moveToEvaluate.IsCapture)
            moveHistoryTable[plyFromRoot & 1, (int)moveToEvaluate.MovePieceType, moveToEvaluate.TargetSquare.Index] += 1 << searchDepth;
          break;
        }
        if (eval > alpha)
          alpha = eval;
      }
    }
    // </tree search>
    transpositionTable[key & tableEntries] = new TTEntry(key,
                                       (short)bestScore,
                                       (sbyte)searchDepth,
                                       bestMove,
                                       (byte)(bestScore >= beta ? 1 : bestScore <= alpha ? 2 : 0));

    return bestScore;
  }

  public Move Think(Board board, Timer timer) {
    globalBoard = board;
    globalTimer = timer;
    moveHistoryTable = new int[2, 7, 64];
    int rootEval = -maximumScore, alpha = -maximumScore, beta = maximumScore, iterativeSearchDepth = 0;
    Span<Move> legalMoves = stackalloc Move[256];
    board.GetLegalMovesNonAlloc(ref legalMoves);
    Span<int> moveScores = stackalloc int[legalMoves.Length];
    while (timer.MillisecondsElapsedThisTurn < TimeRemaining / 2 && iterativeSearchDepth < 50) {
      moveScores.Fill(-maximumScore);
      for (int i = legalMoves.Length - 1; i >= 0; i--) {
        board.MakeMove(legalMoves[i]);
        moveScores[i] = -SearchPosition(iterativeSearchDepth, 1, alpha, beta);
        board.UndoMove(legalMoves[i]);
        if (moveScores[i] > rootEval) {
          rootEval = moveScores[i];
          if (rootEval > alpha)
            alpha = rootEval;
          if (alpha >= beta)
            break;
        }
      }
      moveScores.Sort(legalMoves);
      if (rootEval < alpha)
        alpha = -maximumScore;
      else if (rootEval > beta)
        beta = maximumScore;
      else {
        alpha = rootEval - 197;
        beta = rootEval + 197;
        ++iterativeSearchDepth;
      }
    }
#if DEBUG
    Console.WriteLine("M : " + rootEval);
#endif
    return legalMoves[^1];
  }
}
// Command for cutechess
// "C:\Program Files (x86)\Cute Chess\cutechess-cli.exe" -engine name="New" cmd="./Chess-Challenge" arg="uci" arg="NarvvhalBot" -engine name="Old" cmd="./Chess-Challenge" arg="uci" arg="EvilBot" -each proto=uci tc=1+0.08 -concurrency 5 -maxmoves 200 -rounds 2500 -ratinginterval 20 -repeat 2 -sprt elo0=0 elo1=10 alpha=0.05 beta=0.05 -games 2 -openings file="book.pgn" order=random -recover