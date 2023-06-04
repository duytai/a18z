contract X {mapping(uint256 => uint256) old_balances;uint256 old_z;
  mapping(uint => uint) balances;
  uint z;
  /// ensures(true, balances[z] == old(balances[z]) + 1)
  function sub(uint x) public returns(uint) {(bool __v1, bool __v2)=(true, balances[z] == old_balances[z] + 1);
    balances[z] += 1;
  }
}
