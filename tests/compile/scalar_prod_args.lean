/-!
Check recursive scalar product arguments, shared results, and partial applications.
-/

abbrev State := UInt32 × UInt32 × UInt32 × UInt32

def step (s : State) : State :=
  (s.2.1 + 1, s.2.2.1 + 2, s.2.2.2 + 3, s.1 + 4)

def iterate : Nat → State → State
  | 0, s => s
  | n + 1, s => iterate n (step s)

def loop (n : Nat) (s : State) : State := Id.run do
  let mut s := s
  for _ in [:n] do s := step s
  return s

def mixed : Nat → UInt32 × String → UInt32 × String
  | 0, s => s
  | n + 1, s => mixed n (s.1 + 1, s.2 ++ "x")

def wide : Nat → UInt64 × UInt8 → UInt64 × UInt8
  | 0, s => s
  | n + 1, s => wide n (s.1 + 1, s.2 + 3)

def twoStates : Nat → UInt32 × UInt32 → UInt32 × UInt32 → UInt32 × UInt32
  | 0, a, b => (a.1 + b.1, a.2 + b.2)
  | n + 1, a, b => twoStates n (a.2, a.1) (b.2, b.1)

def floating : Nat → Float × Float → Float × Float
  | 0, s => s
  | n + 1, s => floating n (s.1 + 0.5, s.2 - 0.25)

def main : IO Unit := do
  let initial : State := (10, 20, 30, 40)
  for n in [0, 1, 2, 4, 1000] do
    unless iterate n initial == loop n initial do
      throw (IO.userError "recursive and loop results differ")
  unless iterate 4 initial == (20, 30, 40, 50) do
    throw (IO.userError "incorrect scalar state")
  let partialApplication := iterate 4
  let results := [initial, initial].map partialApplication
  unless results == [(20, 30, 40, 50), (20, 30, 40, 50)] do
    throw (IO.userError "incorrect partial application")
  unless initial == (10, 20, 30, 40) do
    throw (IO.userError "shared input was modified")
  unless mixed 3 (7, "a") == (10, "axxx") do
    throw (IO.userError "incorrect mixed product")
  unless wide 3 (0xfffffffffffffffe, 250) == (1, 3) do
    throw (IO.userError "incorrect wide or narrow scalar")
  unless twoStates 3 (1, 2) (10, 20) == (22, 11) do
    throw (IO.userError "incorrect multiple product arguments")
  unless floating 4 (1.0, 2.0) == (3.0, 1.0) do
    throw (IO.userError "incorrect floating point product")
  IO.println "ok"
