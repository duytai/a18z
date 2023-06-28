contract A {
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, z == 9)
    function a() public {
        z = 10;
        b();
        balances[msg.sender] = 100;
    }
    /// ensures(true, z == 11)
    function b() public {
        z = 11;
    }
}