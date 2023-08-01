/**
 *Submitted for verification at Etherscan.io on 2018-02-27
*/

// pragma solidity 0.4.19;

contract Token {

    /// @return total amount of tokens
    /// ensures(true, true)
    function totalSupply() constant returns (uint supply) {(bool __v1, bool __v2)=(true,  true);}

    /// @param _owner The address from which the balance will be retrieved
    /// @return The balance
    /// ensures(true, true)
    function balanceOf(address _owner) constant returns (uint balance) {(bool __v1, bool __v2)=(true,  true);}

    /// @notice send `_value` token to `_to` from `msg.sender`
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    /// ensures(true, true)
    function transfer(address _to, uint _value) returns (bool success) {(bool __v1, bool __v2)=(true,  true);require(_value >= 0);}

    /// @notice send `_value` token to `_to` from `_from` on the condition it is approved by `_from`
    /// @param _from The address of the sender
    /// @param _to The address of the recipient
    /// @param _value The amount of token to be transferred
    /// @return Whether the transfer was successful or not
    /// ensures(true, true)
    function transferFrom(address _from, address _to, uint _value) returns (bool success) {(bool __v1, bool __v2)=(true,  true);require(_value >= 0);}

    /// @notice `msg.sender` approves `_addr` to spend `_value` tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @param _value The amount of wei to be approved for transfer
    /// @return Whether the approval was successful or not
    /// ensures(true, true)
    function approve(address _spender, uint _value) returns (bool success) {(bool __v1, bool __v2)=(true,  true);require(_value >= 0);}

    /// @param _owner The address of the account owning tokens
    /// @param _spender The address of the account able to transfer the tokens
    /// @return Amount of remaining tokens allowed to spent
    /// ensures(true, true)
    function allowance(address _owner, address _spender) constant returns (uint remaining) {(bool __v1, bool __v2)=(true,  true);}

    event Transfer(address indexed _from, address indexed _to, uint _value);
    event Approval(address indexed _owner, address indexed _spender, uint _value);
}

contract RegularToken is Token {mapping(address => uint256) old_balances;mapping(address => mapping(address => uint256)) old_allowed;uint256 old_totalSupply;
    /// ensures(balances[msg.sender] >= _value && balances[_to] + _value >= balances[_to] && msg.sender != _to, balances[msg.sender] == old(balances[msg.sender]) - _value && balances[_to] == old(balances[_to]) + _value)
    function transfer(address _to, uint _value) returns (bool) {(bool __v1, bool __v2)=(balances[msg.sender] >= _value && balances[_to] + _value >= balances[_to] && msg.sender != _to,  balances[msg.sender] == old_balances[msg.sender] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
        //Default assumes totalSupply can't be over max (2^256 - 1).
        if (balances[msg.sender] >= _value && balances[_to] + _value >= balances[_to]) {
            balances[msg.sender] -= _value;
            balances[_to] += _value;
            Transfer(msg.sender, _to, _value);
            return true;
        } else { return false; }
    }
    /// ensures(allowed[_from][msg.sender] >= _value && balances[_from] >= _value && balances[_to] + _value >= balances[_to] && _from != _to, balances[_from] == old(balances[_from]) - _value && balances[_to] == old(balances[_to]) + _value && allowed[_from][msg.sender] == old(allowed[_from][msg.sender]) - _value)
    function transferFrom(address _from, address _to, uint _value) returns (bool) {(bool __v1, bool __v2)=(allowed[_from][msg.sender] >= _value && balances[_from] >= _value && balances[_to] + _value >= balances[_to] && _from != _to,  balances[_from] == old_balances[_from] - _value && balances[_to] == old_balances[_to] + _value && allowed[_from][msg.sender] == old_allowed[_from][msg.sender] - _value);require(_value >= 0);
        if (balances[_from] >= _value && allowed[_from][msg.sender] >= _value && balances[_to] + _value >= balances[_to]) {
            balances[_to] += _value;
            balances[_from] -= _value;
            allowed[_from][msg.sender] -= _value;
            Transfer(_from, _to, _value);
            return true;
        } else { return false; }
    }
    /// ensures(true, r == balances[_owner])
    function balanceOf(address _owner) constant returns (uint r) {(bool __v1, bool __v2)=(true,  r == balances[_owner]);
        return balances[_owner];
    }
    /// ensures(true, allowed[msg.sender][_spender] == _value)
    function approve(address _spender, uint _value) returns (bool) {(bool __v1, bool __v2)=(true,  allowed[msg.sender][_spender] == _value);require(_value >= 0);
        allowed[msg.sender][_spender] = _value;
        Approval(msg.sender, _spender, _value);
        return true;
    }
    /// ensures(true, r == allowed[_owner][_spender])
    function allowance(address _owner, address _spender) constant returns (uint r) {(bool __v1, bool __v2)=(true,  r == allowed[_owner][_spender]);
        return allowed[_owner][_spender];
    }

    mapping (address => uint) balances;
    mapping (address => mapping (address => uint)) allowed;
    uint public totalSupply;
}

contract UnboundedRegularToken is RegularToken {uint256 old_MAX_UINT;

    uint constant MAX_UINT = 2**256 - 1;
    
    /// @dev ERC20 transferFrom, modified such that an allowance of MAX_UINT represents an unlimited amount.
    /// @param _from Address to transfer from.
    /// @param _to Address to transfer to.
    /// @param _value Amount to transfer.
    /// @return Success of transfer.
    /// ensures(allowed[_from][msg.sender] < MAX_UINT && allowed[_from][msg.sender] >= _value && balances[_from] >= _value && balances[_to] + _value >= balances[_to] && _from != _to, balances[_from] == old(balances[_from]) - _value && balances[_to] == old(balances[_to]) + _value && allowed[_from][msg.sender] == old(allowed[_from][msg.sender]) - _value)
    function transferFrom(address _from, address _to, uint _value)
        public
        returns (bool)
    {(bool __v1, bool __v2)=(allowed[_from][msg.sender] < MAX_UINT && allowed[_from][msg.sender] >= _value && balances[_from] >= _value && balances[_to] + _value >= balances[_to] && _from != _to,  balances[_from] == old_balances[_from] - _value && balances[_to] == old_balances[_to] + _value && allowed[_from][msg.sender] == old_allowed[_from][msg.sender] - _value);require(_value >= 0);require(MAX_UINT >= 0);
        uint allowance = allowed[_from][msg.sender];
        if (balances[_from] >= _value
            && allowance >= _value
            && balances[_to] + _value >= balances[_to]
        ) {
            balances[_to] += _value;
            balances[_from] -= _value;
            if (allowance < MAX_UINT) {
                allowed[_from][msg.sender] -= _value;
            }
            Transfer(_from, _to, _value);
            return true;
        } else {
            return false;
        }
    }
}

contract HBToken is UnboundedRegularToken {uint256 old_totalSupply;uint8 old_decimals;string old_name;string old_symbol;

    uint public totalSupply = 5*10**26;
    uint8 constant public decimals = 18;
    string constant public name = "HuobiToken";
    string constant public symbol = "HT";
    /// ensures(true, balances[msg.sender] == totalSupply)
    function HBToken() {(bool __v1, bool __v2)=(true,  balances[msg.sender] == totalSupply);require(totalSupply >= 0);
        balances[msg.sender] = totalSupply;
        Transfer(address(0), msg.sender, totalSupply);
    }
}