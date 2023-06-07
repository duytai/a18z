contract X {mapping(address => uint256) old_balances;
    mapping(address => uint) balances;

    /// ensures(true, c == a - b)
    function add(uint a, uint b) returns(uint c) {(bool __v1, bool __v2)=(true, c == a - b);require(a >= 0);require(b >= 0);
        require(a >= b);
        c = a + b;
    }

    /// ensures(_amount == 0, balances[_to] == old(balances[_to]) + _amount)
    function transfer(address _to, uint _amount) {(bool __v1, bool __v2)=(_amount == 0, balances[_to] == old_balances[_to] + _amount);require(_amount >= 0);
        balances[_to] = add(balances[_to], _amount);
    }
}