# fen

A Rust Forsyth-Edwards notation parser with proper error handling.

```rust
extern crate fen;

let fen = "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1";
let board = fen::BoardState::from_fen(fen).unwrap();
assert_eq!(fen, board.to_fen());
```
