/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

import R0sy
import Zkvm.Algebra.Classes
import Zkvm.ArithVM.Circuit
import Zkvm.Constants
import Zkvm.MethodId
import Zkvm.Seal.CheckCommitments
import Zkvm.Seal.Fri
import Zkvm.Seal.Header
import Zkvm.Seal.TraceCommitments
import Zkvm.Verify.Error
import Zkvm.Verify.ReadIop

namespace Zkvm.Verify

open R0sy.Hash
open R0sy.Lean.Nat
open Zkvm.Algebra.Classes
open Zkvm.ArithVM.Circuit
open Zkvm.MethodId
open Zkvm.Seal
open Zkvm.Verify.Error
open Zkvm.Verify.ReadIop


def verify [Hash D] (circuit: Circuit) (method_id: MethodId D) (journal: Array UInt32) {M: Type -> Type} [Monad M] [MonadExceptOf VerificationError M] [MonadReadIop M] [MonadCommitIop D M]: M Unit
  := do -- Read the header and verify the journal
        let header <- Header.read circuit
        Header.verify_journal D header journal
        -- Returns error if zkvm execution exceeds cycle limit
        if header.po2 > Constants.MAX_CYCLES_PO2 then throw (VerificationError.TooManyCycles header.po2 Constants.MAX_CYCLES_PO2)
        -- Read the trace commitments and set entropy for generating constraint batching randomness (alpha_constraints)
        let trace_commitments <- TraceCommitments.read_and_commit D circuit header method_id
        -- Read the validity (aka checkpoly) commitments and set entropy for generating random DEEP query point (z)
        let check_commitments <- CheckCommitments.read_and_commit D circuit header trace_commitments.mix
        -- FRI verify
        -- TODO: re-name combo_mix to FRI batching randomness (alpha_FRI)
        let combo_mix: circuit.field.ExtElem <- Field.random
        let tap_cache := circuit.tap_cache combo_mix
        let combo_u := check_commitments.compute_combos tap_cache
        let fri_verify_params <- Fri.read_and_commit D circuit header.size
        Fri.verify fri_verify_params (fun idx
          => do let rows: Array (Array circuit.field.Elem) := #[
                  <- trace_commitments.accum_merkle.verify idx,
                  <- trace_commitments.code_merkle.verify idx,
                  <- trace_commitments.data_merkle.verify idx
                ]
                let check_row: Array circuit.field.Elem <- check_commitments.check_merkle.verify idx
                pure <| tap_cache.eval_taps
                          combo_u
                          header.back_one
                          check_commitments.z
                          rows
                          check_row
                          (Algebra.ofBase (header.fri_gen ^ idx))
        )
        -- Ensure proof buffer is empty
        MonadReadIop.verifyComplete

end Zkvm.Verify
