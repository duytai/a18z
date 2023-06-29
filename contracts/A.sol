contract A {
  mapping(address => mapping(address => uint)) allowed;

  /// ensures(true, false)
  function test(address to, uint amount) public {
    allowed[msg.sender][to] = amount;
  }
}