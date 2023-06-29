contract A {
  mapping(address => uint256) balances;

  /// ensures(true, balances[msg.sender] == old(balances)[msg.sender] - _value && balances[_to] == old(balances)[_to] + _value)
  function transfer(address _to, uint256 _value) returns(bool success) {
    if (balances[msg.sender] >= _value) {
      balances[msg.sender] -= _value;
      balances[_to] += _value;
      return true;
    } else {
      return false;
    }
  }
}