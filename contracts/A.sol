contract A {
    uint z;
    mapping(address => uint) balances;
    /// ensures(true, balances[msg.sender] == 100)
    function a() public {
        z = 10;
        balances[msg.sender] = 100;
        b();
    }
    /// ensures(true, z == 11 && balances[msg.sender] == 100)
    function b() public {
        z = 11;
        balances[msg.sender] += 100;
    }
}