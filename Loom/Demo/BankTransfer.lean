import Loom.Triple.Basic
import Loom.Tactic.VCGen
import Loom.Demo.Specs

open Lean.Order Std.Do'

universe u v

abbrev Limit := Nat

structure Account where
  balance : Nat
  withdrawToday : Limit

inductive TransferError where
  | insufficientFunds (available requested : Nat)
  deriving Repr, BEq

inductive AuditError where
  | limitExceeded (limit requested : Nat)
  deriving Repr, BEq

abbrev BankM := ExceptT AuditError <| ReaderT Limit <| ExceptT TransferError <| StateM Account

def getBalances : BankM Nat := do
  let account ← get
  return account.balance

@[lspec]
theorem spec_getBalances :
    ⦃ fun dayLimit acc => post acc.balance dayLimit acc ⦄
      getBalances
    ⦃ post ⦄ := by
  unfold getBalances
  mvcgen' with grind


def getWithdrawToday : BankM Nat := do
  let account ← get
  return account.withdrawToday

@[lspec]
theorem spec_getWithdrawToday :
    ⦃ fun dayLimit acc => post acc.withdrawToday dayLimit acc ⦄
      getWithdrawToday
    ⦃ post ⦄ := by
  unfold getWithdrawToday
  mvcgen' with grind



def setBalances (balance : Nat) : BankM PUnit := do
  modify fun account => { account with balance }

@[lspec]
theorem spec_setBalances :
    ⦃ fun dayLimit acc => post ⟨⟩ dayLimit { acc with balance } ⦄
      setBalances balance
    ⦃ post ⦄ := by
  unfold setBalances
  mvcgen' with grind



def setWithdrawToday (withdrawToday : Nat) : BankM PUnit := do
  modify fun account => { account with withdrawToday }

@[lspec]
theorem spec_setWithdrawToday :
    ⦃ fun dayLimit acc => post ⟨⟩ dayLimit { acc with withdrawToday } ⦄
      setWithdrawToday withdrawToday
    ⦃ post ⦄ := by
  unfold setWithdrawToday
  mvcgen' with grind


def getLimit : BankM Limit := read

@[lspec]
theorem spec_getLimit :
    ⦃ fun dayLimit acc => post dayLimit dayLimit acc ⦄
      getLimit
    ⦃ post ⦄ := by
  unfold getLimit
  mvcgen' with grind



def withdraw (amount : Nat) : BankM PUnit := do
  let withdrawToday ← getWithdrawToday
  let dailyLimit ← read
  if amount + withdrawToday > dailyLimit then
    throwThe AuditError <| .limitExceeded dailyLimit amount
  let balance ← getBalances
  if balance < amount then
    throwThe TransferError <| .insufficientFunds balance amount
  setBalances <| balance - amount
  setWithdrawToday <| withdrawToday + amount

#synth
  WPMonad BankM
      (Limit → Account → Prop)
    EPost⟨
      AuditError → Limit → Account → Prop,
      TransferError → Account → Prop⟩

theorem spec_withdraw (amount : Nat) (accOld : Account) :
    ⦃ fun _ acc => acc = accOld ⦄
      withdraw amount
    ⦃ fun _ dayLimit acc =>
        acc.balance + amount = accOld.balance ∧
        acc.withdrawToday = accOld.withdrawToday + amount ∧
        amount + accOld.withdrawToday ≤ dayLimit;
      fun _ dayLimit acc =>
        acc.balance = accOld.balance ∧
        acc.withdrawToday + amount > dayLimit;
      fun _ acc =>
        acc.balance = accOld.balance ∧
        amount > acc.balance ⦄ := by
  unfold withdraw
  mvcgen' with grind
