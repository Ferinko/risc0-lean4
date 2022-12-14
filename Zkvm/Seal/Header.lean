/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

import R0sy
import Zkvm.ArithVM.Circuit
import Zkvm.Verify.Error
import Zkvm.Verify.ReadIop

namespace Zkvm.Seal.Header

open R0sy.Algebra
open R0sy.Hash.Sha2
open R0sy.Lean.Nat
open R0sy.Lean.UInt32
open R0sy.Serial
open Zkvm.ArithVM.Circuit
open Zkvm.Verify.Error
open Zkvm.Verify.ReadIop

structure Header (Elem: Type) where
  po2: Nat
  size: Nat
  domain: Nat
  back_one: Elem
  output: Array Elem
  deserialized_output: Array UInt32


def read [Monad M] [MonadReadIop M] [PrimeField Elem] [RootsOfUnity Elem] (circuit: Circuit): M (Header Elem)
  := do let output <- MonadReadIop.readFields Elem circuit.output_size
        let mut deserialized_output := Array.mkEmpty (output.size / 2)
        for i in [0:output.size / 2] do
          let hi := PrimeField.toNat output[2 * i + 1]!
          let lo := PrimeField.toNat output[2 * i]!
          deserialized_output := deserialized_output.push ((hi <<< 16) ||| lo).toUInt32
        let po2 <- MonadReadIop.readU32s 1 >>= (fun x => pure <| x[0]!.toNat)
        let size := 1 <<< po2
        let domain := Constants.INV_RATE * size
        let back_one := RootsOfUnity.ROU_REV[po2]!
        pure {
          po2,
          size,
          domain,
          back_one,
          output,
          deserialized_output
        }

def verify_journal_size [Monad M] [MonadExceptOf VerificationError M] [PrimeField Elem] (self: Header Elem) (journal: Array UInt32): M Unit
  := do let output_len_idx := self.deserialized_output.size - 1
        let output_len := self.deserialized_output[output_len_idx]!.toNat
        let journal_len := journal.size * 4
        if output_len != journal_len
          then throw (VerificationError.SealJournalLengthMismatch output_len journal_len)

def verify_journal [Monad M] [MonadExceptOf VerificationError M] [PrimeField Elem] (self: Header Elem) (journal: Array UInt32): M Unit
  := do verify_journal_size self journal
        let journal := if journal.size <= 8 then journal else Sha256.Digest.toSubarray (Sha256.hash_pod journal)
        for i in [0:journal.size] do
          let s := self.deserialized_output[i]!
          let j := journal[i]!
          if j != s then throw (VerificationError.JournalSealRootMismatch i s j)
        pure ()

end Zkvm.Seal.Header