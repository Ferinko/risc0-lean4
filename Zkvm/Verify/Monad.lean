/-
Copyright (c) 2022 RISC Zero. All rights reserved.
-/

import R0sy.Algebra
import R0sy.Hash.Sha2
import Zkvm.Circuit
import Zkvm.Taps
import Zkvm.Verify.Adapter
import Zkvm.Verify.Classes
import Zkvm.Verify.Fri
import Zkvm.Verify.Merkle
import Zkvm.Verify.ReadIop

namespace Zkvm.Verify.Monad

open R0sy.Algebra
open R0sy.Hash.Sha2
open Adapter
open Circuit
open Classes
open Fri
open Merkle
open ReadIop
open Taps


structure VerifyContext (Elem ExtElem: Type) where
  circuit: Circuit Elem ExtElem
  adapter: VerifyAdapter Elem
  read_iop: ReadIop


class MonadVerify (Elem ExtElem: Type) (M: Type -> Type)
  extends
    MonadStateOf (VerifyContext Elem ExtElem) M,
    MonadExceptOf VerificationError M
  where

instance
  [MonadStateOf (VerifyContext Elem ExtElem) M]
  [MonadExceptOf VerificationError M]
  : MonadVerify Elem ExtElem M where


instance [Monad M] [MonadStateOf (VerifyContext Elem ExtElem) M] : MonadCircuit Elem ExtElem M where
  getCircuit
    := do let self <- get
          return self.circuit

/-
instance [Monad M] [MonadStateOf VerifyContext M] : MonadStateOf Circuit M where
  get
    := do let self <- get
          return self.circuit
  set circuit
    := do let self <- get
          set { self with circuit }
  modifyGet f
    := do let self <- get
          let (result, circuit) := f self.circuit
          set { self with circuit }
          return result
-/

instance [Monad M] [MonadStateOf (VerifyContext Elem ExtElem) M] : MonadStateOf ReadIop M where
  get
    := do let self <- get
          return self.read_iop
  set read_iop
    := do let self <- get
          set { self with read_iop }
  modifyGet f
    := do let self <- get
          let (result, read_iop) := f self.read_iop
          set { self with read_iop }
          return result

instance [Monad M] [MonadStateOf (VerifyContext Elem ExtElem) M] : MonadStateOf (VerifyAdapter Elem) M where
  get
    := do let self <- get
          return self.adapter
  set adapter
    := do let self <- get
          set { self with adapter }
  modifyGet f
    := do let self <- get
          let (result, adapter) := f self.adapter
          set { self with adapter }
          return result


def VerifyContext.run [Field Elem] (circuit: Circuit Elem ExtElem) (seal: Subarray UInt32)
  (f: {M: Type -> Type} -> [Monad M] -> [MonadVerify Elem ExtElem M] -> [Field Elem] -> M Unit)
  : Id (Except VerificationError Unit)
  := do let verify_context: VerifyContext Elem ExtElem := {
          circuit,
          adapter := VerifyAdapter.new,
          read_iop := ReadIop.new seal,
        }
        let M := StateT (VerifyContext Elem ExtElem) (ExceptT VerificationError Id)
        ExceptT.run (StateT.run' (@f M _ _ _) verify_context)

end Zkvm.Verify.Monad
