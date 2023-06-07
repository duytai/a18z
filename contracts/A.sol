contract X {
    mapping(address => uint) balances;

    /// ensures(true, c == a - b)
    function add(uint a, uint b) returns(uint c) {
        require(a >= b);
        c = a + b;
    }

    /// ensures(_amount == 0, balances[_to] == old(balances[_to]) + _amount)
    function transfer(address _to, uint _amount) {
        balances[_to] = add(balances[_to], _amount);
    }
}