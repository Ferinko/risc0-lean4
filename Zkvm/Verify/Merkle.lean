/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

import R0sy.Hash
import R0sy.Hash.Sha2
import R0sy.Lean.Nat
import Zkvm.Verify.Classes

namespace Zkvm.Verify.Merkle

open R0sy.Hash
open R0sy.Hash.Sha2
open R0sy.Lean.Nat
open Classes

structure MerkleTreeParams where
  row_size: Nat
  col_size: Nat
  queries: Nat
  layers: Nat
  top_layer: Nat
  top_size: Nat
  deriving Inhabited

def MerkleTreeParams.new (row_size col_size queries: Nat): MerkleTreeParams :=
  let layers: Nat := Nat.log2_floor row_size
  let top_layer: Nat := Nat.log2_floor queries
  let top_size: Nat := 1 <<< top_layer
  if 1 <<< layers != row_size
  then panic "row_size not a power of 2"
  else
    {
      row_size,
      col_size,
      queries,
      layers,
      top_layer,
      top_size
    }

def MerkleTreeParams.idx_to_top (self: MerkleTreeParams) (idx: Nat): Nat := idx - self.top_size

def MerkleTreeParams.idx_to_rest (_self: MerkleTreeParams) (idx: Nat): Nat := idx - 1

namespace Examples

def ex_1: MerkleTreeParams := MerkleTreeParams.new 1024 1234 50

#eval ex_1.layers == 10
#eval ex_1.top_layer == 5
#eval ex_1.top_size == 32

def ex_2: MerkleTreeParams := MerkleTreeParams.new 2048 31337 128

#eval ex_2.layers == 11
#eval ex_2.top_layer == 7
#eval ex_2.top_size == 128

end Examples


structure MerkleTreeVerifier where
  params: MerkleTreeParams
  top: Array Sha256.Digest
  rest: Array Sha256.Digest

def MerkleTreeVerifier.root (self: MerkleTreeVerifier): Sha256.Digest
  := if self.rest.size == 0
      then self.top[MerkleTreeParams.idx_to_top self.params 1]!
      else self.rest[MerkleTreeParams.idx_to_rest self.params 1]!

def MerkleTreeVerifier.new [Monad M] [MonadReadIop M] (row_size col_size queries: Nat): M MerkleTreeVerifier
  := do let params := MerkleTreeParams.new row_size col_size queries
        let top <- MonadReadIop.readPodSlice Sha256.Digest params.top_size
        let rest := sorry
        let verifier: MerkleTreeVerifier := {
          params,
          top,
          rest
        }
        MonadReadIop.commit (MerkleTreeVerifier.root verifier)
        pure verifier

def MerkleTreeVerifier.verify [Monad M] [MonadReadIop M] [MonadExceptOf VerificationError M] [MonadStateOf Nat M] [R0sy.Algebra.Field Elem] 
  (self: MerkleTreeVerifier) (idx_: Nat): M (Array Elem)
  := do let mut idx := idx_
        if idx >= 2 * self.params.row_size 
          then throw (VerificationError.MerkleQueryOutOfRange idx self.params.row_size) 
          else
        let out <- MonadReadIop.readFields Elem self.params.col_size
        let mut cur := Hash.hash_pod out
        idx := idx + self.params.row_size
        while idx >= 2 * self.params.row_size do
          let low_bit := idx % 2
          let otherArray <- MonadReadIop.readPodSlice Sha256.Digest 1
          let other := otherArray[0]!
          idx := idx / 2
          if low_bit == 1 
          then 
            cur := Hash.hash_pair other cur
          else 
            cur := Hash.hash_pair cur other
        let present_hash := 
          if idx >= self.params.top_size 
            then self.top[self.params.idx_to_top idx]!
            else self.top[self.params.idx_to_rest idx]!
        if present_hash == cur 
        then
          return out
        else 
          throw VerificationError.InvalidProof

end Zkvm.Verify.Merkle
