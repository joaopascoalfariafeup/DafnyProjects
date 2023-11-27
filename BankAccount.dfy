/* 
* Formal specification and verification of a bank account.
* Used to illustration the verification of object-oriented programs and design by contract.
* FEUP, MIEIC, MFES, 2020/21.
*/


class BankAccount {
    var balance: real
    
    // class invariant
    predicate Valid()
      reads this
    {
        balance >= 0.0
    }
 
    constructor (initialBalance: real)
      requires initialBalance >= 0.0
      ensures Valid() 
      ensures balance == initialBalance
    {
        balance := initialBalance;
    }
 
    function getBalance() : real
      reads this
      requires Valid()
    {
      balance
    }

    method deposit(amount : real)
      requires Valid() && amount > 0.0
      modifies this
      ensures Valid() && balance == old(balance) + amount
    {
        balance := balance + amount;
    }

    method withdraw(amount : real)
      requires Valid() && 0.0 < amount <= balance
      modifies this
      ensures Valid() && balance == old(balance) - amount
    {
        balance := balance - amount;
    }

    method transfer(amount : real, destination: BankAccount)
      requires Valid() && destination.Valid() 
      requires 0.0 < amount <= balance && destination != this
      modifies this, destination
      ensures balance == old(balance) - amount
      ensures destination.balance == old(destination.balance) + amount
      ensures Valid() && destination.Valid()  
    {
        this.balance := this.balance - amount;
        destination.balance:= destination.balance + amount;
    }
}

// A simple test case.
method testBankAccount()
{
    var a := new BankAccount(10.0);
    assert a.getBalance() == 10.0;

    var b := new BankAccount(0.0);
    assert b.getBalance() == 0.0;

    a.deposit(10.0);
    assert a.getBalance() == 20.0;

    a.withdraw(5.0);
    assert a.getBalance() == 15.0;

    a.transfer(15.0, b);
    assert a.getBalance() == 0.0;
    assert b.getBalance() == 15.0;
}
