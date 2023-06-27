contract A {
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, z == 10)
    function a() public {
        z = 10;
        b();
        balances[address(0)] = 30;
    }

    /// ensures(true, z >= 20)
    function b() public {
        z = 21;
    }

    function ok() public {
        z = 40;
    }
}