//! This module provides a pretty straightfoward interface for converting
//! [Forsyth-Edwards notation][1] (FEN) into the state of a game of chess and
//! back.
//!
//! FEN is a way of representing a board a string. This crate provides one such
//! representation, `fen::BoardState`. If you want to be able to read FEN, you
//! will to need to create a way to convert `BoardState` to your own board
//! representation.  If you want to export FEN, you will need to convert your
//! own board representation to `BoardState`.
//!
//! [1]: https://en.wikipedia.org/wiki/Forsyth%E2%80%93Edwards_Notation

/// The state of a board. You can convert this to and from FEN.
#[derive(Debug, Eq, PartialEq)]
pub struct BoardState {
    /// The locations of pieces on the board. This vector must be guaranteed to
    /// contain 64 elements.
    ///
    /// Indices start at the bottom left of the board, going from left to right
    /// then down to up. Index 0 represents a1, index 1 represents b1, index
    /// 8 represents a2, ..., index 63 represents h8.
    ///
    /// If `pieces[n]` is `None`, then that means there is no piece on the `n`th
    /// square.
    pub pieces: Vec<Option<Piece>>,

    /// The side that will play next. Since white goes first in standard chess,
    /// this should be `Color::White` in the initial position.
    pub side_to_play: Color,

    /// Whether white can still castle kingside at some time.
    pub white_can_oo: bool,

    /// Whether white can still castle queenside at some time.
    pub white_can_ooo: bool,

    /// Whether black can still castle kingside at some time.
    pub black_can_oo: bool,

    /// Whether black can still castle queenside at some time.
    pub black_can_ooo: bool,

    /// The en passant target square. If the last move was a two-square pawn
    /// move, this will be the position "behind" the pawn. Otherwise, this will
    /// be `None`.
    ///
    /// See the documentation for `BoardState.pieces` for how squares on the
    /// board are indexed.
    pub en_passant_square: Option<u8>,

    /// Number of half-moves (aka "ply") since the last capture or pawn move. If
    /// this number is greater than or equal to 50, then either side may claim
    /// draw by the [fifty-move rule][1].
    ///
    /// [1]: https://en.wikipedia.org/wiki/Fifty-move_rule
    pub halfmove_clock: u64,

    /// Number of full moves since the beginning of the game. This value begins
    /// at 1 and is incremented after black makes a move.
    pub fullmove_number: u64
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Piece {
    pub kind: PieceKind,
    pub color: Color
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PieceKind {
    Pawn,
    Knight,
    Bishop,
    Rook,
    Queen,
    King
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Color {
    White,
    Black
}

pub type FenResult<'a, T> = Result<T, FenError<'a>>;

#[derive(Debug, Eq, PartialEq)]
pub enum FenError<'a> {
    NotEnoughParts,
    BadPlacement(&'a str),
    TooManyPieces(&'a str),
    UnknownPiece(char),
    NoSuchSide(&'a str),
    BadEnPassant(&'a str),
    BadHalfmove(&'a str),
    BadFullmove(&'a str),
}

impl BoardState {
    /// Create a `BoardState` from a string in Forsyth-Edwards notation.
    ///
    /// ```
    /// // this represents the board after the move 1. e4
    /// let fen = "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1";
    /// let board = fen::BoardState::from_fen(fen).unwrap();
    ///
    /// // 'e' is the fourth file, '3' is the second rank (due to zero-indexing)
    /// //
    /// // See docs for BoardState.pieces for information about indexing
    /// assert_eq!(board.en_passant_square, Some(4 + 2 * 8));
    /// ```
    pub fn from_fen<'a>(fen: &'a str) -> FenResult<'a, BoardState> {
        let parts: Vec<_> = fen.split(' ').collect();
        if parts.len() != 6 {
            return Err(FenError::NotEnoughParts);
        }

        let pieces = try!(Self::parse_placement(parts[0]));
        let side_to_play = try!(Self::parse_side_to_play(parts[1]));
        let (white_can_oo, white_can_ooo, black_can_oo, black_can_ooo) =
            try!(Self::parse_castling(parts[2]));
        let en_passant_square = try!(Self::parse_en_passant(parts[3]));
        let halfmove_clock = try!(Self::parse_halfmove(parts[4]));
        let fullmove_number = try!(Self::parse_fullmove(parts[5]));

        Ok(BoardState {
            pieces: pieces,
            side_to_play: side_to_play,
            white_can_oo: white_can_oo,
            white_can_ooo: white_can_ooo,
            black_can_oo: black_can_oo,
            black_can_ooo: black_can_ooo,
            en_passant_square: en_passant_square,
            halfmove_clock: halfmove_clock,
            fullmove_number: fullmove_number
        })
    }

    fn parse_placement(placement_str: &str) -> FenResult<Vec<Option<Piece>>> {
        let mut placement = vec![None; 64];
        let lines: Vec<_> = placement_str.split('/').collect();

        if lines.len() != 8 {
            return Err(FenError::BadPlacement(placement_str));
        }

        for (rank, pieces) in lines.iter().rev().enumerate() {
            let mut file = 0;

            for piece_char in pieces.chars() {
                match piece_char.to_digit(10) {
                    // This is indicating a few blanks
                    Some(n) => {
                        try!(Self::increment_file(&mut file, n as usize, pieces));
                    }

                    // This is indicating a piece
                    None => {
                        match Piece::from_char(piece_char) {
                            Some(piece) => {
                                placement[rank * 8 + file] = Some(piece);
                                file += 1;
                            },

                            None => return Err(FenError::UnknownPiece(piece_char))
                        }
                    }
                }
            }
        }

        Ok(placement)
    }

    // Attempt to increment `file` by `n`. If this causes file to overflow, then
    // an error is returned.
    fn increment_file<'a>(file: &mut usize, n: usize, rank: &'a str) -> FenResult<'a, ()> {
        *file += n;
        if *file > 8 {
            Err(FenError::TooManyPieces(rank))
        } else {
            Ok(())
        }
    }

    fn parse_side_to_play(side_to_play: &str) -> FenResult<Color> {
        match side_to_play {
            "w" => Ok(Color::White),
            "b" => Ok(Color::Black),
            _ => Err(FenError::NoSuchSide(side_to_play))
        }
    }

    fn parse_castling(castling: &str) -> FenResult<(bool, bool, bool, bool)> {
        let white_oo = castling.contains('K');
        let white_ooo = castling.contains('Q');
        let black_oo = castling.contains('k');
        let black_ooo = castling.contains('q');

        Ok((white_oo, white_ooo, black_oo, black_ooo))
    }

    fn parse_en_passant(en_passant: &str) -> FenResult<Option<u8>> {
        if en_passant == "-" {
            return Ok(None);
        }

        if en_passant.len() != 2 {
            return Err(FenError::BadEnPassant(en_passant));
        }

        let chars: Vec<_> = en_passant.chars().collect();
        let (file, rank) = (chars[0], chars[1]);

        let file = match file {
            'a' => 0,
            'b' => 1,
            'c' => 2,
            'd' => 3,
            'e' => 4,
            'f' => 5,
            'g' => 6,
            'h' => 7,
            _ => return Err(FenError::BadEnPassant(en_passant))
        };

        let rank = match rank {
            '1' => 0,
            '2' => 1,
            '3' => 2,
            '4' => 3,
            '5' => 4,
            '6' => 5,
            '7' => 6,
            '8' => 7,
            _ => return Err(FenError::BadEnPassant(en_passant))
        };

        Ok(Some(file + rank * 8))
    }

    fn parse_halfmove(halfmove: &str) -> FenResult<u64> {
        match halfmove.parse() {
            Ok(n) => Ok(n),
            Err(_) => Err(FenError::BadHalfmove(halfmove))
        }
    }

    fn parse_fullmove(fullmove: &str) -> FenResult<u64> {
        match fullmove.parse() {
            Ok(n) => Ok(n),
            Err(_) => Err(FenError::BadFullmove(fullmove))
        }
    }

    /// Convert a BoardState into a string in Forsyth-Edwards notation.
    ///
    /// ```
    /// let fen = "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1";
    /// let board = fen::BoardState::from_fen(fen).unwrap();
    /// assert_eq!(fen, board.to_fen());
    /// ```
    pub fn to_fen(&self) -> String {
        let placement = self.make_placement();
        let side_to_play = self.make_side_to_play();
        let castling = self.make_castling();
        let en_passant = self.make_en_passant();
        let halfmove = self.make_halfmove();
        let fullmove = self.make_fullmove();

        let parts = [placement, side_to_play, castling,
                     en_passant, halfmove, fullmove];
        parts.connect(" ")
    }

    fn make_placement(&self) -> String {
        let mut placement = String::new();

        for rank in (0..8).rev() {
            let mut blanks = 0;

            for file in 0..8 {
                match self.pieces[rank * 8 + file] {
                    Some(ref piece) => {
                        if blanks != 0 {
                            placement.push_str(&blanks.to_string());
                            blanks = 0;
                        }

                        placement.push_str(&piece.to_string());
                    }

                    None => { blanks += 1 }
                }
            }

            if blanks != 0 {
                placement.push_str(&blanks.to_string());
            }

            // rank = 0 is the last rank displayed, and does not need a '/'
            // separator
            if rank != 0 {
                placement.push('/');
            }
        }

        placement
    }

    fn make_side_to_play(&self) -> String {
        match self.side_to_play {
            Color::White => "w",
            Color::Black => "b"
        }.to_owned()
    }

    fn make_castling(&self) -> String {
        let mut castling = String::new();
        if self.white_can_oo  { castling.push('K') }
        if self.white_can_ooo { castling.push('Q') }
        if self.black_can_oo  { castling.push('k') }
        if self.black_can_ooo { castling.push('q') }

        if castling != "" {
            castling
        } else {
            "-".to_owned()
        }
    }

    fn make_en_passant(&self) -> String {
        match self.en_passant_square {
            Some(en_passant) => {
                let file = match en_passant % 8 {
                    0 => 'a',
                    1 => 'b',
                    2 => 'c',
                    3 => 'd',
                    4 => 'e',
                    5 => 'f',
                    6 => 'g',
                    7 => 'h',
                    _ => unreachable!()
                };

                let rank = match en_passant / 8 {
                    0 => '1',
                    1 => '2',
                    2 => '3',
                    3 => '4',
                    4 => '5',
                    5 => '6',
                    6 => '7',
                    7 => '8',
                    _ => unreachable!()
                };

                format!("{}{}", file, rank)
            },

            None => "-".to_owned()
        }
    }

    fn make_halfmove(&self) -> String {
        self.halfmove_clock.to_string()
    }

    fn make_fullmove(&self) -> String {
        self.fullmove_number.to_string()
    }
}

impl Piece {
    pub fn from_char(piece_char: char) -> Option<Piece> {
        let (color, kind) = match piece_char {
            'P' => (Color::White, PieceKind::Pawn),
            'N' => (Color::White, PieceKind::Knight),
            'B' => (Color::White, PieceKind::Bishop),
            'R' => (Color::White, PieceKind::Rook),
            'Q' => (Color::White, PieceKind::Queen),
            'K' => (Color::White, PieceKind::King),
            'p' => (Color::Black, PieceKind::Pawn),
            'n' => (Color::Black, PieceKind::Knight),
            'b' => (Color::Black, PieceKind::Bishop),
            'r' => (Color::Black, PieceKind::Rook),
            'q' => (Color::Black, PieceKind::Queen),
            'k' => (Color::Black, PieceKind::King),
            _ => return None
        };

        Some(Piece { color: color, kind: kind })
    }
}

impl ToString for Piece {
    fn to_string(&self) -> String {
        match (&self.color, &self.kind) {
            (&Color::White, &PieceKind::Pawn) => "P",
            (&Color::White, &PieceKind::Knight) => "N",
            (&Color::White, &PieceKind::Bishop) => "B",
            (&Color::White, &PieceKind::Rook) => "R",
            (&Color::White, &PieceKind::Queen) => "Q",
            (&Color::White, &PieceKind::King) => "K",
            (&Color::Black, &PieceKind::Pawn) => "p",
            (&Color::Black, &PieceKind::Knight) => "n",
            (&Color::Black, &PieceKind::Bishop) => "b",
            (&Color::Black, &PieceKind::Rook) => "r",
            (&Color::Black, &PieceKind::Queen) => "q",
            (&Color::Black, &PieceKind::King) => "k"
        }.to_owned()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test_valid_fen(fen: &str) {
        let board = BoardState::from_fen(fen).unwrap();
        assert_eq!(fen, board.to_fen());
    }

    #[test]
    fn test_to_and_from_fen() {
        test_valid_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        test_valid_fen("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1");
        test_valid_fen("rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6 0 2");
        test_valid_fen("rnbqkbnr/pp1ppppp/8/2p5/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 1 2");
        test_valid_fen("4k3/8/8/8/8/8/4P3/4K3 w - - 5 39");
    }

    #[test]
    fn test_too_short() {
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::NotEnoughParts), board);
    }

    #[test]
    fn test_bad_placement() {
        let placement = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR/8";
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR/8 w KQkq - 0 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::BadPlacement(placement)), board);
    }

    #[test]
    fn test_too_many_pieces() {
        let fen = "rnbqkbnr/pppppppp/9/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::TooManyPieces("9")), board);
    }

    #[test]
    fn test_unknown_piece() {
        let fen = "rnbqkbnr/ppppTppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::UnknownPiece('T')), board);
    }

    #[test]
    fn test_no_such_side() {
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR n KQkq - 0 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::NoSuchSide("n")), board);
    }

    #[test]
    fn test_bad_en_passant() {
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq h9 0 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::BadEnPassant("h9")), board);
    }

    #[test]
    fn test_bad_halfmove() {
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - zero 1";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::BadHalfmove("zero")), board);
    }

    #[test]
    fn test_bad_fullmove() {
        let fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 one";
        let board = BoardState::from_fen(fen);
        assert_eq!(Err(FenError::BadFullmove("one")), board);
    }
}
