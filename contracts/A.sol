contract A {
  mapping(address => uint) balances;
  
  /// ensures(a >= b, c == a - b)
  function subtract(uint256 a, uint256 b) returns(uint c) {
    assert(a >= b);
    return a - b;
  }

  /// ensures(true, balances[msg.sender]==old(balances[msg.sender])-_value && balances[_to]==old(balances[_to])+_value)
  function transfer(address _to, uint256 _value) public returns(bool success) {
    assert(_value >= 10);
    if (_value > 0) {
      balances[msg.sender] = subtract(balances[msg.sender], _value);
      balances[_to] += _value;
      return true;
    } else {
      return false;
    }
  }
}


