contract X {
  mapping(uint => uint) balances;
  uint z;
  /// ensures(true, balances[z] == old(balances[z]) + 1)
  function sub(uint x) public returns(uint) {
    balances[z] = balances[z] + 1;
  }
}
