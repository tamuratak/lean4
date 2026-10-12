import Lean

namespace Sha256ProbeBaseline

private def constants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] private def rotate (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def referenceBlocks (state : Array UInt32) (bytes : ByteArray) : Array UInt32 := Id.run do
  let mut state := state
  for block in [:bytes.size / 64] do
    let mut words : Array UInt32 := Array.replicate 64 0
    for i in [:16] do
      let offset := block * 64 + i * 4
      let mut word : UInt32 := 0
      for j in [:4] do word := (word <<< 8) ||| bytes[offset + j]!.toUInt32
      words := words.set! i word
    for i in [16:64] do
      let x := words[i - 15]!
      let y := words[i - 2]!
      words := words.set! i (words[i - 16]! +
        (rotate x 7 ^^^ rotate x 18 ^^^ (x >>> 3)) + words[i - 7]! +
        (rotate y 17 ^^^ rotate y 19 ^^^ (y >>> 10)))
    let mut a := state[0]!
    let mut b := state[1]!
    let mut c := state[2]!
    let mut d := state[3]!
    let mut e := state[4]!
    let mut f := state[5]!
    let mut g := state[6]!
    let mut h := state[7]!
    for i in [:64] do
      let t1 := h + (rotate e 6 ^^^ rotate e 11 ^^^ rotate e 25) +
        ((e &&& f) ^^^ ((~~~e) &&& g)) + constants[i]! + words[i]!
      let t2 := (rotate a 2 ^^^ rotate a 13 ^^^ rotate a 22) +
        ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
      h := g; g := f; f := e; e := d + t1
      d := c; c := b; b := a; a := t1 + t2
    let next := #[a, b, c, d, e, f, g, h]
    for i in [:8] do state := state.set! i (state[i]! + next[i]!)
  return state

end Sha256ProbeBaseline

def main (args : List String) : IO Unit := do
  let count := (args.headD "65536").toNat!
  let mut bytes := ByteArray.mk (Array.replicate count 0)
  if args[1]? == some "pattern" then
    for i in [:count] do bytes := bytes.set! i ((i * 37 + 11) % 256).toUInt8
  let initial : Array UInt32 := #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let start ← IO.monoNanosNow
  let result := Sha256ProbeBaseline.referenceBlocks initial bytes
  let stop ← IO.monoNanosNow
  IO.println s!"state={result.toList}"
  IO.println s!"bytes={count} elapsed_ns={stop - start}"
