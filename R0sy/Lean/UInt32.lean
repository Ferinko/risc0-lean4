/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

namespace R0sy.Lean.UInt32

/- Endian helpers -/

def UInt32.swap_endian (x: UInt32): UInt32 :=
  let a0 := x &&& 0xff
  let a1 := (x >>> (8*1)) &&& 0xff
  let a2 := (x >>> (8*2)) &&& 0xff
  let a3 := (x >>> (8*3)) &&& 0xff
  let c0 := a0 <<< (8*3)
  let c1 := a1 <<< (8*2)
  let c2 := a2 <<< (8*1)
  let c3 := a3
  c3 ||| c2 ||| c1 ||| c0

def UInt32.ror (x: UInt32) (n: Nat): UInt32 :=
  let l := x >>> UInt32.ofNat n
  let r := x <<< UInt32.ofNat (32 - n)
  l ||| r

def UInt32.of_be32 (b3 b2 b1 b0: UInt8): UInt32 :=
  let c0 := UInt32.ofNat (b0.val.val)
  let c1 := UInt32.ofNat (b1.val.val) <<< (8*1)
  let c2 := UInt32.ofNat (b2.val.val) <<< (8*2)
  let c3 := UInt32.ofNat (b3.val.val) <<< (8*3)
  c3 ||| c2 ||| c1 ||| c0

end R0sy.Lean.UInt32