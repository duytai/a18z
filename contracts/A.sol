contract A {
  mapping(address => uint) balances;
  ///ensures(true, balances[msg.sender]==old(balances[msg.sender])-_value && balances[_to]==old(balances[_to])+_value)
  function transfer(address _to, uint256 _value) public returns(bool success) {
    if (balances[msg.sender] >= _value && _value > 0) {
      balances[msg.sender] -= _value;
      balances[_to] += _value;
      return true;
    } else {
      return false;
    }
  }
}