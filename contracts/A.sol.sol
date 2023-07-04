contract A {mapping(address => uint256) old_balances;
  mapping(address => uint) balances;
  
  /// ensures(a >= b, c == a - b)
  function subtract(uint256 a, uint256 b) returns(uint c) {(bool __v1, bool __v2)=(a >= b,  c == a - b);require(a >= 0);require(b >= 0);
    assert(a >= b);
    return a - b;
  }

  /// ensures(true, balances[msg.sender]==old(balances[msg.sender])-_value && balances[_to]==old(balances[_to])+_value)
  function transfer(address _to, uint256 _value) public returns(bool success) {(bool __v1, bool __v2)=(true,  balances[msg.sender]==old_balances[msg.sender]-_value && balances[_to]==old_balances[_to]+_value);require(_value >= 0);
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


