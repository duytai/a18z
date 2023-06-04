contract X {
  mapping(uint => uint) balances;
  uint z;
  /// ensures(x >= y, r == x - y && z == old(z) + 20)
  function sub(uint x, uint y) private returns(uint r) {
    r = x - y;
    z = z + 20;
  }

  /// ensures(z >= 10, z == old(z) + 20)
  function test() public {
    sub(30, 10);
  }
}
