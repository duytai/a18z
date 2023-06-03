contract X {
  mapping(uint => uint) balances;
  mapping(uint => uint) old_balances;
  uint z;
  uint old_z;
  function sub(uint x, uint y) public returns(uint r) {
    (bool __v1, bool __v2) = (z == 0, z == old_z + 20);
    if (x > 10) {
      z = z + 20;
    } else {
      z = 20;
    }
  }

  function test(uint x) public {
    (bool __v1, bool __v2) = (true, balances[0] == old_balances[x] - 0);
    if (x > 0) {
      balances[x] = sub(balances[x], 0);
    } else {
      x = 20;
    }
  }
}
