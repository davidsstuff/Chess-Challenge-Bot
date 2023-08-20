using ChessChallenge.API;
using System;
using System.Numerics;

public class MyBot : IChessBot {
  record struct TTEntry(uint Key,
                        short Score,
                        sbyte Depth,
                        Move BestMove,
                        byte Flag);

  int[] pieceValues = { 0, 89, 313, 324, 494, 872, 20000 };
  Board globalBoard;
  int tableEntries = (1 << 23) - 1;
  TTEntry[] transpositionTable = new TTEntry[1 << 23];
  int[,,] moveHistoryTable;
  Move _bestMove;
  int TimeRemaining => globalTimer.MillisecondsRemaining / 50;
  int maximumScore = 300000, bishopIncrease = 44, startingDepth = 1, mobilityWeight = 9, aspirationWindow = 412;
  Timer globalTimer;

  public int RawEvaluation() {
    int score = 0, squareIndex;

    foreach (bool isWhitePiece in new[] { true, false }) {
      // 1 = Pawn, 2 = Knight, 3 = Bishop, 4 = Rook, 5 = Queen, 6 = King
      for (int piece = 1; piece <= 6; piece++) {
        ulong mask = globalBoard.GetPieceBitboard((PieceType)piece, isWhitePiece);
        if (piece == 3 && BitOperations.PopCount(mask) > 1)
          score += bishopIncrease;
        while (mask != 0) {
          score += pieceValues[piece];
          ulong mobilityBitboard = 0ul;
          squareIndex = BitboardHelper.ClearAndGetIndexOfLSB(ref mask);
          Square square = new(squareIndex);
          switch (piece) {
            case 1:
              mobilityBitboard = BitboardHelper.GetPawnAttacks(square, isWhitePiece);
              break;
            case 2:
              mobilityBitboard = BitboardHelper.GetKnightAttacks(square);
              ulong enemyPawnBitboard = globalBoard.GetPieceBitboard(PieceType.Pawn, !isWhitePiece);
              while (enemyPawnBitboard != 0)
                mobilityBitboard &= ~BitboardHelper.GetPawnAttacks(new Square(BitboardHelper.ClearAndGetIndexOfLSB(ref enemyPawnBitboard)), !isWhitePiece);
              break;
            case 3:
            case 4:
            case 5:
              mobilityBitboard = BitboardHelper.GetSliderAttacks((PieceType)piece, square, globalBoard);
              break;
            default:
              break;
          }
          score += BitOperations.PopCount(mobilityBitboard) * mobilityWeight;
        }
      }

      score = -score;
    }

    return score * (globalBoard.IsWhiteToMove ? 1 : -1);
  }

  int SearchPosition(int searchDepth, int plyFromRoot, int alpha, int beta, int totalExtensions) {
    if (globalBoard.IsDraw() && plyFromRoot > 0)
      return 0;
    if (globalBoard.IsInCheckmate())
      return -maximumScore + plyFromRoot;
    uint key = (uint)(globalBoard.ZobristKey >> 32);
    TTEntry currentTableEntry = transpositionTable[key & tableEntries];

    bool isEntryKeyCorrect = currentTableEntry.Key == key, 
      isPVNode = beta - alpha > 1, canReduceNode = false, 
      isQuiescenceSearch = searchDepth <= 0, 
      isPlayerInCheck = globalBoard.IsInCheck();
    int bestScore = -maximumScore, eval = 0, zeroWidthBeta, extension = totalExtensions < 16 && isPlayerInCheck ? 1 : 0;

    int Search(int newBeta, int r = 0) => eval = -SearchPosition(searchDepth - 1 + extension - r, plyFromRoot + 1, -newBeta, -alpha, totalExtensions + extension);
    if (isEntryKeyCorrect && currentTableEntry.Depth >= searchDepth && plyFromRoot > 0) {
      switch (currentTableEntry.Flag) {
        case 0:
          return currentTableEntry.Score;
        case 1:
          alpha = Math.Max(alpha, currentTableEntry.Score);
          break;
        case 2:
          beta = Math.Min(beta, currentTableEntry.Score);
          break;
      }
      if (alpha >= beta)
        return currentTableEntry.Score;
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
      canReduceNode = searchDepth >= 3;

      globalBoard.TrySkipTurn();
      Search(beta, 2);
      globalBoard.UndoSkipTurn();
      if (eval >= beta)
        return eval;
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
    zeroWidthBeta = beta;
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
        if (plyFromRoot == 0)
          _bestMove = bestMove;
      }
      zeroWidthBeta = alpha + 1;
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
    int rootEval, alpha = -aspirationWindow, beta = aspirationWindow, iterativeSearchDepth = startingDepth;
    while (timer.MillisecondsElapsedThisTurn < TimeRemaining / 2) {
      rootEval = SearchPosition(iterativeSearchDepth, 0, alpha, beta, 0);
      if (rootEval < alpha)
        alpha = -maximumScore;
      else if (rootEval > beta)
        beta = maximumScore;
      else {
        alpha = rootEval - aspirationWindow;
        beta = rootEval + aspirationWindow;
        ++iterativeSearchDepth;
      }
    }
#if DEBUG
    Console.WriteLine("M : " + iterativeSearchDepth);
#endif
    return _bestMove;
  }
}
// Command for cutechess
// "C:\Program Files (x86)\Cute Chess\cutechess-cli.exe" -engine name="New" cmd="./Chess-Challenge" arg="uci" arg="NarvvhalBot" -engine name="Old" cmd="./Chess-Challenge" arg="uci" arg="EvilBot" -each proto=uci tc=8+0.08 -concurrency 5 -maxmoves 200 -rounds 2500 -ratinginterval 20 -repeat 2 -sprt elo0=0 elo1=10 alpha=0.05 beta=0.05 -games 2 -openings file="Scand3Qd6-Qd8.pgn" order=random -recover