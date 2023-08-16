using ChessChallenge.API;
using System;

public class MyBot : IChessBot {
  struct TTEntry {
    public ulong key;
    public int score, depth, flag;
    // Flag values: 0=VALID, 1=LBOUND, 2=UBOUND
    public Move bestMove;

    public TTEntry(ulong _key, int _score, int _depth, Move _bestMove, int _flag) {
      key = _key;
      score = _score;
      depth = _depth;
      bestMove = _bestMove;
      flag = _flag;
    }
  }

  int[] pieceVal = { 0, 100, 300, 300, 500, 900, 20000 };
  Board _board;
  const ulong entries = (1 << 19) - 1;
  TTEntry[] table = new TTEntry[entries];
  int[,,] history;
  Move _bestMove;
  int timeRemaining, maxNum = 300000;
  Timer _timer;

  int[] piecePhase = { 0, 0, 1, 1, 2, 4, 0 };
  ulong[] psts = { 657614902731556116, 420894446315227099, 384592972471695068, 312245244820264086, 364876803783607569, 366006824779723922, 366006826859316500, 786039115310605588, 421220596516513823, 366011295806342421, 366006826859316436, 366006896669578452, 162218943720801556, 440575073001255824, 657087419459913430, 402634039558223453, 347425219986941203, 365698755348489557, 311382605788951956, 147850316371514514, 329107007234708689, 402598430990222677, 402611905376114006, 329415149680141460, 257053881053295759, 291134268204721362, 492947507967247313, 367159395376767958, 384021229732455700, 384307098409076181, 402035762391246293, 328847661003244824, 365712019230110867, 366002427738801364, 384307168185238804, 347996828560606484, 329692156834174227, 365439338182165780, 386018218798040211, 456959123538409047, 347157285952386452, 365711880701965780, 365997890021704981, 221896035722130452, 384289231362147538, 384307167128540502, 366006826859320596, 366006826876093716, 366002360093332756, 366006824694793492, 347992428333053139, 457508666683233428, 329723156783776785, 329401687190893908, 366002356855326100, 366288301819245844, 329978030930875600, 420621693221156179, 422042614449657239, 384602117564867863, 419505151144195476, 366274972473194070, 329406075454444949, 275354286769374224, 366855645423297932, 329991151972070674, 311105941360174354, 256772197720318995, 365993560693875923, 258219435335676691, 383730812414424149, 384601907111998612, 401758895947998613, 420612834953622999, 402607438610388375, 329978099633296596, 67159620133902 };

  int GetPstVal(int psq) => (int)(((psts[psq / 10] >> (6 * (psq % 10))) & 63) - 20) * 8;

  int Evaluate(int colour) {
    int mg = 0, eg = 0, phase = 0;

    foreach (bool stm in new[] { true, false }) {
      for (var p = PieceType.Pawn; p <= PieceType.King; p++) {
        int piece = (int)p, ind;
        ulong mask = _board.GetPieceBitboard(p, stm);
        while (mask != 0) {
          phase += piecePhase[piece];
          ind = 128 * (piece - 1) + BitboardHelper.ClearAndGetIndexOfLSB(ref mask) ^ (stm ? 56 : 0);
          mg += GetPstVal(ind) + pieceVal[piece];
          eg += GetPstVal(ind + 64) + pieceVal[piece];
        }
      }

      mg = -mg;
      eg = -eg;
    }

    return (mg * phase + eg * (24 - phase)) / 24 * colour;
  }

  int SearchFunction(int searchDepth, int colour, int movesMade, int alpha, int beta) {
    if (movesMade > 0 && _board.IsRepeatedPosition())
      return 0;
    ulong key = _board.ZobristKey;
    TTEntry entry = table[key % entries];
    int bestScore = -maxNum, eval, b; // promote to a queen, whilst taking a queen

    var legalMoves = _board.GetLegalMoves(searchDepth <= 0);

    if (searchDepth > 0 && legalMoves.Length == 0)
      return _board.IsInCheckmate() ? -maxNum + movesMade : 0;

    bool isEntryKeyCorrect = entry.key == key;
    if (isEntryKeyCorrect && entry.depth >= searchDepth && movesMade > 0) {
      switch (entry.flag) {
        case 0:
          return entry.score;
        case 1:
          alpha = Math.Max(alpha, entry.score);
          break;
        case 2:
          beta = Math.Min(beta, entry.score);
          break;
      }
      if (alpha >= beta)
        return entry.score;
    }

    // <quiescence search>
    if (searchDepth <= 0) {
      bestScore = Evaluate(colour); // used to be eval, switching to best score improved massively
      if (bestScore > alpha)
        alpha = bestScore;
      if (alpha >= beta)
        return alpha;
    }
    // </quiescence search>

    // <rank moves>
    Move bestMove = isEntryKeyCorrect ? entry.bestMove : Move.NullMove, legalMove;
    var moveScores = new int[legalMoves.Length];
    for (int i = 0; i < legalMoves.Length; i++) {
      legalMove = legalMoves[i];
      // <hash Move />
      if (legalMove == bestMove)
        moveScores[i] = 100000;
      // <mvv-lva />
      else if (legalMove.IsCapture)
        moveScores[i] = 10 * pieceVal[(int)legalMove.CapturePieceType] - pieceVal[(int)legalMove.MovePieceType];
      // <default value />
      else
        moveScores[i] = history[Math.Max(colour, 0), legalMove.StartSquare.Index, legalMove.TargetSquare.Index];
    }
    // </rank moves>

    // <tree search>
    b = beta;
    for (int i = 0; i < legalMoves.Length; i++) {
      // <sort moves>
      for (int j = i + 1; j < legalMoves.Length; j++) {
        if (moveScores[j] > moveScores[i])
          (moveScores[i], moveScores[j], legalMoves[i], legalMoves[j]) = (moveScores[j], moveScores[i], legalMoves[j], legalMoves[i]);
      }
      // </sort moves>

      if (_timer.MillisecondsElapsedThisTurn > timeRemaining)
        return -maxNum;

      legalMove = legalMoves[i];
      _board.MakeMove(legalMove);
      eval = -SearchFunction(searchDepth - 1, -colour, movesMade + 1, -b, -alpha);
      if (eval > alpha && eval < beta && i > 0)
        eval = -SearchFunction(searchDepth - 1, -colour, movesMade + 1, -beta, -alpha);
      _board.UndoMove(legalMove);
      if (eval > bestScore) {
        bestMove = legalMove;
        bestScore = eval;
        if (eval >= beta) {
          if (!legalMove.IsCapture)
            history[Math.Max(colour, 0), legalMove.StartSquare.Index, legalMove.TargetSquare.Index] += 1 << searchDepth;
          break;
        }
        if (eval > alpha)
          alpha = eval;
        if (movesMade == 0 && bestScore != maxNum)
          _bestMove = bestMove;
      }
      b = alpha + 1;
    }
    // </tree search>
    int flag = bestScore >= beta ? 1 : bestScore <= alpha ? 2 : 0;
    table[key % entries] = new TTEntry(key, bestScore, searchDepth, bestMove, flag);

    return bestScore;
  }

  public Move Think(Board board, Timer timer) {
    _board = board;
    _timer = timer;
    history = new int[2, 64, 64];
    int alpha = -50, beta = 50, colour = board.IsWhiteToMove ? 1 : -1, score, epsilon = 50;
    sbyte depth = 1;
    timeRemaining = timer.MillisecondsRemaining / 25;
    while (timer.MillisecondsElapsedThisTurn < timeRemaining / 2) {
      score = SearchFunction(depth, colour, 0, alpha, beta);
      if (score > beta || score < alpha) {
        alpha = -maxNum;
        beta = maxNum;
      } else {
        alpha = score - epsilon;
        beta = score + epsilon;
        ++depth;
      }
    }

    return _bestMove;
  }
}
// Command for cutechess
// "C:\Program Files (x86)\Cute Chess\cutechess-cli.exe" -engine name="NarvvhalsBot" cmd="./Chess-Challenge" arg="uci" arg="NarvvhalBot" -engine name="EvilBot" cmd="./Chess-Challenge" arg="uci" arg="EvilBot" -each proto=uci tc=10+0.1 -concurrency 6 -maxmoves 200 -rounds 500 -ratinginterval 10 -repeat 2 -sprt elo0=0 elo1=10 alpha=0.05 beta=0.05 -games 2