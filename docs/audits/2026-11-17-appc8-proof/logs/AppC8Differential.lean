import CryptidSolvePhase4.AppC8RawShuttle
open CryptidSolvePhase4.AppC8Raw
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def observe (c : Cfg) : State × List Bool :=
  (c.st, ((List.range 8).reverse.map (fun n => read (c.left.drop n))) ++
    ((List.range 9).map (fun n => read (c.right.drop n))))
example : (run 1 ⟨.A, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [false,false,false], [false,false,false,false]⟩).map observe = some (.D, [false,false,false,false,false,false,true,false,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.A, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,true,false,true,true,true,true,true,false,false]) := by decide
example : (run 1 ⟨.A, [true,true,true], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,true,true], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.A, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.A, [true,false,true], [false,false,true,false]⟩).map observe = some (.B, [false,false,false,false,true,false,true,true,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,false,true], [false,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,true,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,false,true], [false,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,true,true,true,true,false]) := by decide
example : (run 19 ⟨.A, [true,false,true], [false,false,true,false]⟩).map observe = some (.E, [false,false,false,true,false,true,false,true,true,true,true,true,false,false,false,false,false]) := by decide
example : (run 1 ⟨.A, [true,true,true], [false,true,true,true]⟩).map observe = some (.B, [false,false,false,false,true,true,true,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,true,true], [false,true,true,true]⟩).map observe = some (.D, [false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,true,true], [false,true,true,true]⟩).map observe = some (.B, [false,false,true,true,true,false,true,false,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.A, [true,true,true], [false,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,false,false,true,true,true,false,true,true,true,true,true]) := by decide
example : (run 1 ⟨.A, [false,false,false], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.A, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,true,true,false,true,true]) := by decide
example : (run 1 ⟨.A, [true,true,true], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,true,true], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.A, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.A, [true,false,true], [true,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,false,true], [true,false,true,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,false,true], [true,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,true,false,true,false,true,true,false,true,false]) := by decide
example : (run 19 ⟨.A, [true,false,true], [true,false,true,false]⟩).map observe = some (.D, [false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.A, [true,true,true], [true,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.A, [true,true,true], [true,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false]) := by decide
example : (run 7 ⟨.A, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.A, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.B, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,true,false,true,true,false,false,false,false,false]) := by decide
example : (run 19 ⟨.B, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,true,false,true,true,false,true,true,false,false,false,false,false]) := by decide
example : (run 1 ⟨.B, [true,true,true], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,true,true], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.B, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.B, [true,false,true], [false,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,false,true], [false,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,false,true], [false,false,true,false]⟩).map observe = some (.D, [false,false,false,false,false,true,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.B, [true,false,true], [false,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,true,false,false,true,true,false,true,true,false,false]) := by decide
example : (run 1 ⟨.B, [true,true,true], [false,true,true,true]⟩).map observe = some (.A, [false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,true,true], [false,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.B, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.B, [false,false,false], [true,false,false,false]⟩).map observe = some (.D, [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [false,false,false], [true,false,false,false]⟩).map observe = some (.E, [false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [false,false,false], [true,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false]) := by decide
example : (run 19 ⟨.B, [false,false,false], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,false,true,true,false,true,true,false,false,false]) := by decide
example : (run 1 ⟨.B, [true,true,true], [true,false,false,false]⟩).map observe = some (.D, [false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,true,true], [true,false,false,false]⟩).map observe = some (.E, [false,false,false,true,true,true,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,true,true], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,false,true,true,true,false,true,true,false,false,false]) := by decide
example : (run 19 ⟨.B, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.B, [true,false,true], [true,false,true,false]⟩).map observe = some (.D, [false,false,false,false,true,false,true,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,false,true], [true,false,true,false]⟩).map observe = some (.E, [false,false,false,true,false,true,false,true,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,false,true], [true,false,true,false]⟩).map observe = some (.E, [true,false,true,false,true,true,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.B, [true,false,true], [true,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,true,false,true,true,true,false,true,true,false,false]) := by decide
example : (run 1 ⟨.B, [true,true,true], [true,true,true,true]⟩).map observe = some (.D, [false,false,false,false,true,true,true,false,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.B, [true,true,true], [true,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,true,true,true,false,true,true,true,false,false,false,false,false]) := by decide
example : (run 7 ⟨.B, [true,true,true], [true,true,true,true]⟩).map observe = some (.D, [false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.B, [true,true,true], [true,true,true,true]⟩).map observe = some (.A, [false,false,true,false,true,false,false,true,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.C, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.C, [false,false,false], [false,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.C, [false,false,false], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,true,false,true,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.C, [true,true,true], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,true,true], [false,false,false,false]⟩).map observe = some (.D, [false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.C, [true,true,true], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,true,true,false,true,true,false,false,false,false]) := by decide
example : (run 19 ⟨.C, [true,true,true], [false,false,false,false]⟩).map observe = some (.D, [false,false,false,true,false,true,false,false,true,true,false,true,true,false,false,false,false]) := by decide
example : (run 1 ⟨.C, [true,false,true], [false,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,true,false,true,false,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,false,true], [false,false,true,false]⟩).map observe = some (.D, [false,false,false,false,false,true,false,false,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.C, [true,false,true], [false,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,true,true,false,true,true,true,false,false,false,false,false]) := by decide
example : (run 19 ⟨.C, [true,false,true], [false,false,true,false]⟩).map observe = some (.E, [false,false,false,false,false,true,false,true,true,true,true,true,true,true,true,true,false]) := by decide
example : (run 1 ⟨.C, [true,true,true], [false,true,true,true]⟩).map observe = some (.B, [false,false,false,false,false,false,true,true,true,false,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,true,true], [false,true,true,true]⟩).map observe = some (.D, [false,false,false,false,false,true,true,false,false,true,true,true,false,false,false,false,false]) := by decide
example : (run 7 ⟨.C, [true,true,true], [false,true,true,true]⟩).map observe = some (.B, [false,false,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.C, [true,true,true], [false,true,true,true]⟩).map observe = some (.D, [true,false,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.C, [false,false,false], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [false,false,false], [true,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.C, [false,false,false], [true,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,true,false,true,true,true,false,false,false]) := by decide
example : (run 19 ⟨.C, [false,false,false], [true,false,false,false]⟩).map observe = some (.E, [false,false,false,false,false,false,false,true,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 1 ⟨.C, [true,true,true], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 7 ⟨.C, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.C, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.C, [true,false,true], [true,false,true,false]⟩).map observe = some (.F, [false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 7 ⟨.C, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 19 ⟨.C, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 1 ⟨.C, [true,true,true], [true,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.C, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 7 ⟨.C, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.C, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.D, [false,false,false], [false,false,false,false]⟩).map observe = some (.E, [false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [false,false,false], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [false,false,false], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false]) := by decide
example : (run 19 ⟨.D, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,true,false,true,true,false,true,true,false,false]) := by decide
example : (run 1 ⟨.D, [true,true,true], [false,false,false,false]⟩).map observe = some (.E, [false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,true,true], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.D, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.D, [true,false,true], [false,false,true,false]⟩).map observe = some (.E, [false,false,false,false,true,false,true,true,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,false,true], [false,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,true,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,false,true], [false,false,true,false]⟩).map observe = none := by decide
example : (run 19 ⟨.D, [true,false,true], [false,false,true,false]⟩).map observe = none := by decide
example : (run 1 ⟨.D, [true,true,true], [false,true,true,true]⟩).map observe = some (.E, [false,false,false,false,true,true,true,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,true,true], [false,true,true,true]⟩).map observe = some (.B, [false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,true,true], [false,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,true,false,true,false,false,false,false]) := by decide
example : (run 19 ⟨.D, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.D, [false,false,false], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.D, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,true,true,false,true,true]) := by decide
example : (run 1 ⟨.D, [true,true,true], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,true,true], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.D, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.D, [true,false,true], [true,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,false,true], [true,false,true,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,false,true], [true,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,true,false,true,false,true,true,false,true,false]) := by decide
example : (run 19 ⟨.D, [true,false,true], [true,false,true,false]⟩).map observe = some (.D, [false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.D, [true,true,true], [true,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.D, [true,true,true], [true,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false]) := by decide
example : (run 7 ⟨.D, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.D, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.E, [false,false,false], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.E, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,true,false,true,true,false,true,true]) := by decide
example : (run 1 ⟨.E, [true,true,true], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,true,true], [false,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.E, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.E, [true,false,true], [false,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,false,true], [false,false,true,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,false,true,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,false,true], [false,false,true,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,true,false,true,false,true,true,false,true,false]) := by decide
example : (run 19 ⟨.E, [true,false,true], [false,false,true,false]⟩).map observe = some (.D, [false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.E, [true,true,true], [false,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,true,true], [false,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,true,true,true,true,true,true,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.E, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.E, [false,false,false], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [false,false,false], [true,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [false,false,false], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.E, [false,false,false], [true,false,false,false]⟩).map observe = some (.C, [false,false,false,false,true,false,true,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 1 ⟨.E, [true,true,true], [true,false,false,false]⟩).map observe = some (.B, [false,false,false,false,true,true,true,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,true,true], [true,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,true,true,true,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,true,true], [true,false,false,false]⟩).map observe = some (.F, [false,false,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.E, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.E, [true,false,true], [true,false,true,false]⟩).map observe = some (.B, [false,false,false,false,true,false,true,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,false,true], [true,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,true,false,true,false,true,true,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,false,true], [true,false,true,false]⟩).map observe = some (.D, [false,false,false,false,true,false,true,false,false,true,false,false,false,false,false,false,false]) := by decide
example : (run 19 ⟨.E, [true,false,true], [true,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,true,false,true,false,true,true,false,true,true,false,false]) := by decide
example : (run 1 ⟨.E, [true,true,true], [true,true,true,true]⟩).map observe = some (.B, [false,false,false,false,true,true,true,false,true,true,true,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.E, [true,true,true], [true,true,true,true]⟩).map observe = some (.D, [false,false,false,true,true,true,false,false,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.E, [true,true,true], [true,true,true,true]⟩).map observe = some (.F, [false,false,false,false,false,false,false,false,true,true,true,true,false,true,true,false,false]) := by decide
example : (run 19 ⟨.E, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [false,false,false], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.F, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.F, [false,false,false], [false,false,false,false]⟩).map observe = some (.B, [false,false,false,false,false,false,false,true,true,false,true,true,false,false,false,false,false]) := by decide
example : (run 19 ⟨.F, [false,false,false], [false,false,false,false]⟩).map observe = some (.F, [false,false,false,false,false,false,false,true,false,true,true,true,true,true,false,false,false]) := by decide
example : (run 1 ⟨.F, [true,true,true], [false,false,false,false]⟩).map observe = some (.A, [false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false,false]) := by decide
example : (run 2 ⟨.F, [true,true,true], [false,false,false,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false,false]) := by decide
example : (run 7 ⟨.F, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [true,true,true], [false,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [true,false,true], [false,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,true,false,true,false,false,true,false,false,false,false,false]) := by decide
example : (run 2 ⟨.F, [true,false,true], [false,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,false,true,false,false,true,false,false,false,false]) := by decide
example : (run 7 ⟨.F, [true,false,true], [false,false,true,false]⟩).map observe = some (.A, [false,false,false,false,false,false,false,true,false,true,false,true,false,false,false,false,false]) := by decide
example : (run 19 ⟨.F, [true,false,true], [false,false,true,false]⟩).map observe = some (.C, [false,false,false,false,false,true,true,false,true,true,false,true,true,false,false,false,false]) := by decide
example : (run 1 ⟨.F, [true,true,true], [false,true,true,true]⟩).map observe = some (.A, [false,false,false,false,false,false,true,true,true,false,true,true,true,false,false,false,false]) := by decide
example : (run 2 ⟨.F, [true,true,true], [false,true,true,true]⟩).map observe = some (.C, [false,false,false,false,false,false,false,true,true,true,false,true,true,true,false,false,false]) := by decide
example : (run 7 ⟨.F, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [true,true,true], [false,true,true,true]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [false,false,false], [true,false,false,false]⟩).map observe = none := by decide
example : (run 2 ⟨.F, [false,false,false], [true,false,false,false]⟩).map observe = none := by decide
example : (run 7 ⟨.F, [false,false,false], [true,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [false,false,false], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 2 ⟨.F, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 7 ⟨.F, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [true,true,true], [true,false,false,false]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 2 ⟨.F, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 7 ⟨.F, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [true,false,true], [true,false,true,false]⟩).map observe = none := by decide
example : (run 1 ⟨.F, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 2 ⟨.F, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 7 ⟨.F, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
example : (run 19 ⟨.F, [true,true,true], [true,true,true,true]⟩).map observe = none := by decide
#eval IO.println "[PASS] 192 independent dictionary/Lean execution fixtures"
