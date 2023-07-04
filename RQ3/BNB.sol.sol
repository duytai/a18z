/**
 *Submitted for verification at Etherscan.io on 2017-07-06
*/

pragma solidity ^0.4.8;

/**
 * Math operations with safety checks
 */
contract SafeMath {
  /// ensures(true, r == a * b)
  function safeMul(uint256 a, uint256 b) internal returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a * b);require(a >= 0);require(b >= 0);
    uint256 c = a * b;
    // assert(a == 0 || c / a == b);
    return c;
  }
  /// ensures(b > 0, r == a / b)
  function safeDiv(uint256 a, uint256 b) internal returns (uint256 r) {(bool __v1, bool __v2)=(b > 0,  r == a / b);require(a >= 0);require(b >= 0);
    assert(b > 0);
    uint256 c = a / b;
    assert(a == b * c + a % b);
    return c;
  }
  /// ensures(a >= b, r == a - b)
  function safeSub(uint256 a, uint256 b) internal returns (uint256 r) {(bool __v1, bool __v2)=(a >= b,  r == a - b);require(a >= 0);require(b >= 0);
    assert(b <= a);
    return a - b;
  }
  /// ensures(true, r == a + b)
  function safeAdd(uint256 a, uint256 b) internal returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a + b);require(a >= 0);require(b >= 0);
    uint256 c = a + b;
    assert(c>=a && c>=b);
    return c;
  }

  // function assert(bool assertion) internal {
  //   if (!assertion) {
  //     throw;
  //   }
  // }
}
contract BNB is SafeMath{string old_name;string old_symbol;uint8 old_decimals;uint256 old_totalSupply;address old_owner;mapping(address => uint256) old_balanceOf;mapping(address => uint256) old_freezeOf;mapping(address => mapping(address => uint256)) old_allowance;
    string public name;
    string public symbol;
    uint8 public decimals;
    uint256 public totalSupply;
	address public owner;

    /* This creates an array with all balances */
    mapping (address => uint256) public balanceOf;
	mapping (address => uint256) public freezeOf;
    mapping (address => mapping (address => uint256)) public allowance;

    /* This generates a public event on the blockchain that will notify clients */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /* This notifies clients about the amount burnt */
    event Burn(address indexed from, uint256 value);
	
	/* This notifies clients about the amount frozen */
    event Freeze(address indexed from, uint256 value);
	
	/* This notifies clients about the amount unfrozen */
    event Unfreeze(address indexed from, uint256 value);

    /* Initializes contract with initial supply tokens to the creator of the contract */
    /// ensures(true, balanceOf[msg.sender] == initialSupply && totalSupply == initialSupply && decimals == decimalUnits && owner == msg.sender)
    function BNB(
        uint256 initialSupply,
        string tokenName,
        uint8 decimalUnits,
        string tokenSymbol
        ) {(bool __v1, bool __v2)=(true,  balanceOf[msg.sender] == initialSupply && totalSupply == initialSupply && decimals == decimalUnits && owner == msg.sender);require(initialSupply >= 0);require(decimalUnits >= 0);
        balanceOf[msg.sender] = initialSupply;              // Give the creator all initial tokens
        totalSupply = initialSupply;                        // Update total supply
        name = tokenName;                                   // Set the name for display purposes
        symbol = tokenSymbol;                               // Set the symbol for display purposes
        decimals = decimalUnits;                            // Amount of decimals for display purposes
		    owner = msg.sender;
    }

    /* Send coins */
    /// ensures(msg.sender != _to && _to != address(0) && _value > 0 && balanceOf[msg.sender] >= _value && balanceOf[_to] >= 0, balanceOf[msg.sender] == old(balanceOf[msg.sender]) - _value && balanceOf[_to] == old(balanceOf[_to]) + _value)
    function transfer(address _to, uint256 _value) {(bool __v1, bool __v2)=(msg.sender != _to && _to != address(0) && _value > 0 && balanceOf[msg.sender] >= _value && balanceOf[_to] >= 0,  balanceOf[msg.sender] == old_balanceOf[msg.sender] - _value && balanceOf[_to] == old_balanceOf[_to] + _value);require(_value >= 0);
        if (_to == 0x0) throw;                               // Prevent transfer to 0x0 address. Use burn() instead
		    if (_value <= 0) throw; 
        if (balanceOf[msg.sender] < _value) throw;           // Check if the sender has enough
        if (balanceOf[_to] + _value < balanceOf[_to]) throw; // Check for overflows
        balanceOf[msg.sender] = SafeMath.safeSub(balanceOf[msg.sender], _value);                     // Subtract from the sender
        balanceOf[_to] = SafeMath.safeAdd(balanceOf[_to], _value);                            // Add the same to the recipient
        Transfer(msg.sender, _to, _value);                   // Notify anyone listening that this transfer took place
    }

    /* Allow another contract to spend some tokens in your behalf */
    /// ensures(_value > 0, allowance[msg.sender][_spender] == _value)
    function approve(address _spender, uint256 _value)
        returns (bool success) {(bool __v1, bool __v2)=(_value > 0,  allowance[msg.sender][_spender] == _value);require(_value >= 0);
		    if (_value <= 0) throw; 
        allowance[msg.sender][_spender] = _value;
        return true;
    }
       

    /* A contract attempts to get the coins */
    /// ensures(_from != _to && balanceOf[_to] >= 0 && _to != address(0) && _value > 0 && balanceOf[_from] >= _value && _value <= allowance[_from][msg.sender], balanceOf[_from] == old(balanceOf[_from]) - _value && balanceOf[_to] == old(balanceOf[_to]) + _value && allowance[_from][msg.sender] == old(allowance[_from][msg.sender]) - _value)
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success) {(bool __v1, bool __v2)=(_from != _to && balanceOf[_to] >= 0 && _to != address(0) && _value > 0 && balanceOf[_from] >= _value && _value <= allowance[_from][msg.sender],  balanceOf[_from] == old_balanceOf[_from] - _value && balanceOf[_to] == old_balanceOf[_to] + _value && allowance[_from][msg.sender] == old_allowance[_from][msg.sender] - _value);require(_value >= 0);
        if (_to == 0x0) throw;                                // Prevent transfer to 0x0 address. Use burn() instead
		    if (_value <= 0) throw; 
        if (balanceOf[_from] < _value) throw;                 // Check if the sender has enough
        if (balanceOf[_to] + _value < balanceOf[_to]) throw;  // Check for overflows
        if (_value > allowance[_from][msg.sender]) throw;     // Check allowance
        balanceOf[_from] = SafeMath.safeSub(balanceOf[_from], _value);                           // Subtract from the sender
        balanceOf[_to] = SafeMath.safeAdd(balanceOf[_to], _value);                             // Add the same to the recipient
        allowance[_from][msg.sender] = SafeMath.safeSub(allowance[_from][msg.sender], _value);
        Transfer(_from, _to, _value);
        return true;
    }
    /// ensures(totalSupply >= _value && balanceOf[msg.sender] >= _value && _value > 0, balanceOf[msg.sender] == old(balanceOf[msg.sender]) - _value && totalSupply == old(totalSupply) - _value)
    function burn(uint256 _value) returns (bool success) {(bool __v1, bool __v2)=(totalSupply >= _value && balanceOf[msg.sender] >= _value && _value > 0,  balanceOf[msg.sender] == old_balanceOf[msg.sender] - _value && totalSupply == old_totalSupply - _value);require(_value >= 0);require(totalSupply >= 0);
        if (balanceOf[msg.sender] < _value) throw;            // Check if the sender has enough
		    if (_value <= 0) throw; 
        balanceOf[msg.sender] = SafeMath.safeSub(balanceOf[msg.sender], _value);                      // Subtract from the sender
        totalSupply = SafeMath.safeSub(totalSupply,_value);                                // Updates totalSupply
        Burn(msg.sender, _value);
        return true;
    }
	
    /// ensures(balanceOf[msg.sender] >= _value && _value > 0 && balanceOf[msg.sender] >= 0 && freezeOf[msg.sender] >= 0, balanceOf[msg.sender] == old(balanceOf[msg.sender]) - _value && freezeOf[msg.sender] == old(freezeOf[msg.sender]) + _value)
  	function freeze(uint256 _value) returns (bool success) {(bool __v1, bool __v2)=(balanceOf[msg.sender] >= _value && _value > 0 && balanceOf[msg.sender] >= 0 && freezeOf[msg.sender] >= 0,  balanceOf[msg.sender] == old_balanceOf[msg.sender] - _value && freezeOf[msg.sender] == old_freezeOf[msg.sender] + _value);require(_value >= 0);
        if (balanceOf[msg.sender] < _value) throw;            // Check if the sender has enough
  		  if (_value <= 0) throw; 
        balanceOf[msg.sender] = SafeMath.safeSub(balanceOf[msg.sender], _value);                      // Subtract from the sender
        freezeOf[msg.sender] = SafeMath.safeAdd(freezeOf[msg.sender], _value);                                // Updates totalSupply
        Freeze(msg.sender, _value);
        return true;
    }
	 
    /// ensures(freezeOf[msg.sender] >= _value && _value > 0 && balanceOf[msg.sender] >= 0 && freezeOf[msg.sender] >= 0, balanceOf[msg.sender] == old(balanceOf[msg.sender]) + _value && freezeOf[msg.sender] == old(freezeOf[msg.sender]) - _value)
	  function unfreeze(uint256 _value) returns (bool success) {(bool __v1, bool __v2)=(freezeOf[msg.sender] >= _value && _value > 0 && balanceOf[msg.sender] >= 0 && freezeOf[msg.sender] >= 0,  balanceOf[msg.sender] == old_balanceOf[msg.sender] + _value && freezeOf[msg.sender] == old_freezeOf[msg.sender] - _value);require(_value >= 0);
      if (freezeOf[msg.sender] < _value) throw;            // Check if the sender has enough
		  if (_value <= 0) throw; 
      freezeOf[msg.sender] = SafeMath.safeSub(freezeOf[msg.sender], _value);                      // Subtract from the sender
		  balanceOf[msg.sender] = SafeMath.safeAdd(balanceOf[msg.sender], _value);
      Unfreeze(msg.sender, _value);
      return true;
    }
	
  	// transfer balance to owner
    /// ensures(msg.sender == owner, true)
  	function withdrawEther(uint256 amount) {(bool __v1, bool __v2)=(msg.sender == owner,  true);require(amount >= 0);
  		if(msg.sender != owner) throw;
  		// owner.transfer(amount);
  	}
  	
  	// can accept ether
    /// ensures(true, true)
  	// function() payable {
    // }
}