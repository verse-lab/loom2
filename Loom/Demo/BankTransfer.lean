import Loom.Triple.Basic
import Loom.Tactic.VCGen
import Loom.Demo.Specs

open Lean.Order Std.Do'

universe u v

structure Balance where
  balance : Nat
  withDrawToday : Nat

abbrev Limit := Nat

inductive TransferError where
  | insufficientFunds (available requested : Nat)
  deriving Repr, BEq

inductive AuditError where
  | limitExceeded (limit requested : Nat)
  deriving Repr, BEq

abbrev BankM := ExceptT AuditError <| ReaderT Limit <| ExceptT TransferError <| StateM Balance

def getBalances : BankM Nat := do
  let account ← get
  return account.balance

@[lspec high]
theorem spec_getBalances
    {post : Nat → Nat → Balance → Prop} :
    ⦃ fun dayLimit acc => post acc.balance dayLimit acc ⦄
      getBalances
    ⦃ post ⦄ := by
  unfold getBalances
  mvcgen' with grind


def getWithDrawToday : BankM Nat := do
  let account ← get
  return account.withDrawToday

@[lspec high]
theorem spec_getWithDrawToday
    {post : Nat → Nat → Balance → Prop} :
    ⦃ fun dayLimit acc => post acc.withDrawToday dayLimit acc ⦄
      getWithDrawToday
    ⦃ post ⦄ := by
  unfold getWithDrawToday
  mvcgen' with grind



def setBalances (balance : Nat) : BankM PUnit := do
  modify fun account => { account with balance }

@[lspec high]
theorem spec_setBalances (balance : Nat)
    {post : PUnit → Nat → Balance → Prop} :
    ⦃ fun dayLimit acc => post ⟨⟩ dayLimit { acc with balance } ⦄
      setBalances balance
    ⦃ post ⦄ := by
  unfold setBalances
  mvcgen' with grind



def setWithDrawToday (withDrawToday : Nat) : BankM PUnit := do
  modify fun account => { account with withDrawToday }

@[lspec high]
theorem spec_setWithDrawToday (withDrawToday : Nat)
    {post : PUnit → Nat → Balance → Prop} :
    ⦃ fun dayLimit acc => post ⟨⟩ dayLimit { acc with withDrawToday } ⦄
      setWithDrawToday withDrawToday
    ⦃ post ⦄ := by
  unfold setWithDrawToday
  mvcgen' with grind


def getLimit : BankM Limit := read

@[lspec high]
theorem spec_getLimit :
    ⦃ fun dayLimit acc => post dayLimit dayLimit acc ⦄
      getLimit
    ⦃ post ⦄ := by
  unfold getLimit
  mvcgen' with grind

#print BankM

def withdraw (amount : Nat) : BankM PUnit := do
  let withDrawToday ← getWithDrawToday
  let dailyLimit ← read
  if amount + withDrawToday > dailyLimit then
    throwThe AuditError <| .limitExceeded dailyLimit amount
  let balance ← getBalances
  if balance < amount then
    throwThe TransferError <| .insufficientFunds balance amount
  setBalances <| balance - amount
  setWithDrawToday <| withDrawToday + amount

#synth
  WP BankM
      (Nat → Balance → Prop)
    EPost⟨
      AuditError → Nat → Balance → Prop,
      TransferError → Balance → Prop⟩

theorem spec_withdraw (amount : Nat)
   (oldBalance : Nat) (oldWithDrawToday : Nat) :
    ⦃ fun _ acc => acc.balance = oldBalance ∧ acc.withDrawToday = oldWithDrawToday ⦄
      withdraw amount
    ⦃ fun _ dayLimit acc =>
        acc.balance + amount = oldBalance ∧
        acc.withDrawToday = oldWithDrawToday + amount ∧
        amount + oldWithDrawToday ≤ dayLimit;
      fun _ dayLimit acc =>
        acc.balance = oldBalance ∧
        acc.withDrawToday + amount > dayLimit;
      fun _ acc =>
        acc.balance = oldBalance ∧
        amount > acc.balance ⦄ := by
  unfold withdraw
  mvcgen' with grind
