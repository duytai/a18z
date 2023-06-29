contract A {mapping(address => mapping(address => uint256)) old_allowed;
  mapping(address => mapping(address => uint)) allowed;

  /// ensures(true, false)
  function test(address to, uint amount) public {(bool __v1, bool __v2)=(true,  false);require(amount >= 0);
    allowed[msg.sender][to] = amount;
  }
}