﻿using System;
using System.Linq;
using System.Numerics;
using ChessChallenge.API;

public class MyBot : IChessBot {
  readonly Move[] _killerMoves = new Move[50];
  readonly int _maximumScore = 30000000;

  readonly int[] _pieceValues =
      { 109, 285, 332, 486, 894, 0, 99, 327, 283, 478, 927, 0 },
    _moveScores = new int[218];

  readonly (uint, short, sbyte, Move, byte)[]
    _transpositionTable = new (uint, short, sbyte, Move, byte)[0x800000]; // 2^23

  readonly int[][] _unpackedPestoTables;
  Move _bestMove;
  int[,,] _moveHistoryTable;
  int _timeRemaining;

  public MyBot() =>
    // Big table packed with data from premade piece square tables
    // Access using using PackedEvaluationTables[square][pieceType] = score
    _unpackedPestoTables = new[] {
      63746705523041458768562654720m, 71818693703096985528394040064m, 75532537544690978830456252672m,
      75536154932036771593352371712m, 76774085526445040292133284352m, 3110608541636285947269332480m,
      936945638387574698250991104m, 75531285965747665584902616832m,
      77047302762000299964198997571m, 3730792265775293618620982364m, 3121489077029470166123295018m,
      3747712412930601838683035969m, 3763381335243474116535455791m, 8067176012614548496052660822m,
      4977175895537975520060507415m, 2475894077091727551177487608m,
      2458978764687427073924784380m, 3718684080556872886692423941m, 4959037324412353051075877138m,
      3135972447545098299460234261m, 4371494653131335197311645996m, 9624249097030609585804826662m,
      9301461106541282841985626641m, 2793818196182115168911564530m,
      77683174186957799541255830262m, 4660418590176711545920359433m, 4971145620211324499469864196m,
      5608211711321183125202150414m, 5617883191736004891949734160m, 7150801075091790966455611144m,
      5619082524459738931006868492m, 649197923531967450704711664m,
      75809334407291469990832437230m, 78322691297526401047122740223m, 4348529951871323093202439165m,
      4990460191572192980035045640m, 5597312470813537077508379404m, 4980755617409140165251173636m,
      1890741055734852330174483975m, 76772801025035254361275759599m,
      75502243563200070682362835182m, 78896921543467230670583692029m, 2489164206166677455700101373m,
      4338830174078735659125311481m, 4960199192571758553533648130m, 3420013420025511569771334658m,
      1557077491473974933188251927m, 77376040767919248347203368440m,
      73949978050619586491881614568m, 77043619187199676893167803647m, 1212557245150259869494540530m,
      3081561358716686153294085872m, 3392217589357453836837847030m, 1219782446916489227407330320m,
      78580145051212187267589731866m, 75798434925965430405537592305m,
      68369566912511282590874449920m, 72396532057599326246617936384m, 75186737388538008131054524416m,
      77027917484951889231108827392m, 73655004947793353634062267392m, 76417372019396591550492896512m,
      74568981255592060493492515584m, 70529879645288096380279255040m,
    }.Select(packedTable =>
      new BigInteger(packedTable).ToByteArray().Take(12)
        // Using search max time since it's an integer than initializes to zero and is assgined before being used again 
        .Select(square => (int)((sbyte)square * 1.461) + _pieceValues[_timeRemaining++ % 12])
        .ToArray()
    ).ToArray();

  public Move Think(Board board, Timer timer) {
    _moveHistoryTable = new int[2, 7, 64];
    _timeRemaining = timer.MillisecondsRemaining / 50;
    for (int alpha = -_maximumScore,
         beta = _maximumScore,
         depth = 1;
         timer.MillisecondsElapsedThisTurn < _timeRemaining / 2;) {
      int score = SearchFunction(depth, 0, alpha, beta);
      if (score < alpha)
        alpha -= 100;
      else if (score > beta)
        beta += 100;
      else {
        alpha = score - 25;
        beta = score + 25;
        ++depth;
      }
    }

    return _bestMove;

    int RawEvaluation() {
      int middlegame = 0, endgame = 0, gamephase = 0, sideToMove = 2, piece;
      for (; --sideToMove >= 0; middlegame = -middlegame, endgame = -endgame)
      for (piece = -1; ++piece < 6;)
      for (ulong mask = board.GetPieceBitboard((PieceType)piece + 1, sideToMove > 0); mask != 0;) {
        // Gamephase, middlegame -> endgame
        gamephase += (0x00042110 >> (piece * 4)) & 0x0F;

        // Material and square evaluation
        int square = BitboardHelper.ClearAndGetIndexOfLSB(ref mask) ^ (56 * sideToMove);
        middlegame += _unpackedPestoTables[square][piece];
        endgame += _unpackedPestoTables[square][piece + 6];
      }

      // Tempo bonus to help with aspiration windows
      return (middlegame * gamephase + endgame * (24 - gamephase)) / 24 * (board.IsWhiteToMove ? 1 : -1) +
             gamephase / 2;
    }

    int SearchFunction(int searchDepth, int movesMade, int alpha, int beta) {
      bool isNotRoot = movesMade > 0,
        isCheck = board.IsInCheck(),
        isQuiescenceSearch = searchDepth <= 0;
      if (board.IsDraw() && isNotRoot)
        return 0;
      if (board.IsInCheckmate())
        return movesMade - _maximumScore;
      uint key = (uint)(board.ZobristKey >> 32);
      ref var entry = ref _transpositionTable[board.ZobristKey & 0x7fffff];
      int bestScore = -_maximumScore, eval, reduction, i = 0;
      if (isCheck)
        searchDepth++;

      bool isEntryKeyCorrect = entry.Item1 == key;
      short entryScore = entry.Item2;
      if (isEntryKeyCorrect && entry.Item3 >= searchDepth && isNotRoot) {
        switch (entry.Item5) {
          case 0:
            return entryScore;
          case 1:
            alpha = Math.Max(alpha, entryScore);
            break;
          case 2:
            beta = Math.Min(beta, entryScore);
            break;
        }

        if (alpha >= beta)
          return entryScore;
      }

      // <quiescence search>
      if (isQuiescenceSearch) {
        bestScore = RawEvaluation();
        if (bestScore >= beta)
          return bestScore;
        if (bestScore > alpha)
          alpha = bestScore;
      }
      // </quiescence search>
      else if (beta - alpha == 1 && !isCheck) {
        eval = RawEvaluation();

        if (searchDepth <= 5 && eval - 100 * searchDepth >= beta)
          return eval;

        if (searchDepth >= 2) {
          board.TrySkipTurn();
          Search(alpha + 1, 3);
          board.UndoSkipTurn();
          if (eval >= beta)
            return eval;
        }
      }

      // <rank moves>
      var bestMove = isEntryKeyCorrect ? entry.Item4 : Move.NullMove;
      Span<Move> legalMoves = stackalloc Move[256];
      board.GetLegalMovesNonAlloc(ref legalMoves, isQuiescenceSearch);
      foreach (var move in legalMoves)
        // <hash Move />
        _moveScores[i++] = -(move == bestMove
          ? 90000000
          : move.IsCapture
            ? 100000 * (int)move.CapturePieceType - (int)move.MovePieceType
            : _killerMoves[movesMade] == move
              ? 999999
              : _moveHistoryTable[movesMade & 1, (int)move.MovePieceType, move.TargetSquare.Index]);
      // </rank moves>
      _moveScores.AsSpan(0, legalMoves.Length).Sort(legalMoves);

      i = 0;
      // <tree search>
      foreach (var move in legalMoves) {
        board.MakeMove(move);
        bool isQuiet = !(move.IsCapture || move.IsPromotion || board.IsInCheck());
        reduction = ++i <= 3 || !isQuiet || isCheck ? 0 : searchDepth / 3;
        if ((isQuiescenceSearch || i == 1 ? eval = alpha + 1 : Search(alpha + 1, reduction)) > alpha)
          Search(beta);
        board.UndoMove(move);

        if (timer.MillisecondsElapsedThisTurn > _timeRemaining && movesMade > 2)
          return _maximumScore;

        if (eval <= bestScore) continue;
        bestScore = eval;
        if (eval > alpha) {
          bestMove = move;
          alpha = eval;
          if (!isNotRoot && alpha != _maximumScore)
            _bestMove = bestMove;
        }

        if (eval < beta) continue;
        if (isQuiet) {
          _moveHistoryTable[movesMade & 1, (int)move.MovePieceType, move.TargetSquare.Index] += 1 << searchDepth;
          _killerMoves[movesMade] = move;
        }

        break;
      }

      // </tree search>
      entry = new(key, (short)bestScore, (sbyte)searchDepth, bestMove,
        (byte)(bestScore >= beta ? 1 : bestScore <= alpha ? 2 : 0));

      return bestScore;

      int Search(int inputBeta, int r = 0) =>
        eval = -SearchFunction(searchDepth - 1 - r, movesMade + 1, -inputBeta, -alpha);
    }
  }
}
// Command for cutechess
// "C:\Program Files (x86)\Cute Chess\cutechess-cli.exe" -engine name="New" cmd="./Chess-Challenge" arg="uci" arg="NarvvhalBot" -engine name="Old" cmd="./Chess-Challenge" arg="uci" arg="EvilBot" -each proto=uci tc=10+0.1 -concurrency 5 -maxmoves 200 -rounds 2500 -ratinginterval 20 -repeat 2 -sprt elo0=0 elo1=10 alpha=0.05 beta=0.05 -games 2 -openings file="book.pgn" order=random -recover