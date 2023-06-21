
// contract A {
//     mapping(uint => mapping(uint => uint)) allowance;
//     /// ensures(true, allowance[0][1] == old(allowance[0][1]) - x)
//     function test(uint x) public {
//         allowance[0][1] -= x;
//     }
// }
contract A {
    mapping(address => bool) isTrusted;
    mapping(address => bool) isBlocked;
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowance;
    /// ensures(true, allowance[_sender][msg.sender] == old(allowance[_sender][msg.sender]) - _amount)
    function transferFrom(address _sender, address _recipient, uint256 _amount) public returns (bool r) {
        _transfer(_sender, _recipient, _amount);
        require(allowance[_sender][msg.sender] >= _amount);
        allowance[_sender][msg.sender] -= _amount;
    }

    /// ensures(true, balances[_sender] == old(balances[_sender]) - _amount && old(allowance[_sender][msg.sender]) == allowance[_sender][msg.sender])
    function _transfer(address _sender, address _recipient, uint256 _amount) internal {
        require(_sender != _recipient);
        require(balances[_sender] >= _amount);
        balances[_sender] -= _amount;
        balances[_recipient] += _amount;
    }
}

contract X is A {
    /// ensures(isTrusted[_recipient] && _amount >= 0, old(allowance[_sender][msg.sender]) == allowance[_sender][msg.sender])
    function transferFrom(address _sender, address _recipient, uint256 _amount) public returns (bool r) {
        require(_recipient != address(0));
        require(!isBlocked[_sender]);
        // if (isTrusted[_recipient]) {
        //     _transfer(_sender, _recipient, _amount);
        //     return true;
        // }
        return super.transferFrom(_sender, _recipient, _amount);
    }
}
