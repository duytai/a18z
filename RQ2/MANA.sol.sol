/**
 *Submitted for verification at Etherscan.io on 2017-08-15
*/

// pragma solidity ^0.4.11;

contract ERC20Basic {uint256 old_totalSupply;
  uint256 public totalSupply;
  function balanceOf(address who) constant returns (uint256);
  function transfer(address to, uint256 value) returns (bool);
  event Transfer(address indexed from, address indexed to, uint256 value);
}

contract Ownable {address old_owner;
  address public owner;


  /**
   * @dev The Ownable constructor sets the original `owner` of the contract to the sender
   * account.
   */
  /// ensures(true, owner == msg.sender)
  function Ownable() {(bool __v1, bool __v2)=(true,  owner == msg.sender);
    owner = msg.sender;
  }


  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }


  /**
   * @dev Allows the current owner to transfer control of the contract to a newOwner.
   * @param newOwner The address to transfer ownership to.
   */
  /// ensures(msg.sender == owner && newOwner != address(0), owner == newOwner)
  function transferOwnership(address newOwner) onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner && newOwner != address(0),  owner == newOwner);
    if (newOwner != address(0)) {
      owner = newOwner;
    }
  }

}

contract Pausable is Ownable {bool old_paused;
  event Pause();
  event Unpause();

  bool public paused = false;


  /**
   * @dev modifier to allow actions only when the contract IS paused
   */
  modifier whenNotPaused() {
    require(!paused);
    _;
  }

  /**
   * @dev modifier to allow actions only when the contract IS NOT paused
   */
  modifier whenPaused {
    require(paused);
    _;
  }

  /**
   * @dev called by the owner to pause, triggers stopped state
   */
  /// ensures(msg.sender == owner && !paused, paused)
  function pause() onlyOwner whenNotPaused returns (bool) {(bool __v1, bool __v2)=(msg.sender == owner && !paused,  paused);
    paused = true;
    Pause();
    return true;
  }

  /**
   * @dev called by the owner to unpause, returns to normal state
   */
  /// ensures(msg.sender == owner && paused, !paused)
  function unpause() onlyOwner whenPaused returns (bool) {(bool __v1, bool __v2)=(msg.sender == owner && paused,  !paused);
    paused = false;
    Unpause();
    return true;
  }
}

contract ERC20 is ERC20Basic {
  function allowance(address owner, address spender) constant returns (uint256);
  function transferFrom(address from, address to, uint256 value) returns (bool);
  function approve(address spender, uint256 value) returns (bool);
  event Approval(address indexed owner, address indexed spender, uint256 value);
}

library SafeMath {
  /// ensures(true, r == a * b)
  function mul(uint256 a, uint256 b) internal constant returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a * b);require(a >= 0);require(b >= 0);
    uint256 c = a * b;
    // assert(a == 0 || c / a == b);
    return c;
  }
  /// ensures(true, r == a / b)
  function div(uint256 a, uint256 b) internal constant returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a / b);require(a >= 0);require(b >= 0);
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }
  /// ensures(a >= b, r == a - b)
  function sub(uint256 a, uint256 b) internal constant returns (uint256 r) {(bool __v1, bool __v2)=(a >= b,  r == a - b);require(a >= 0);require(b >= 0);
    assert(b <= a);
    return a - b;
  }
  /// ensures(true, r == a + b)
  function add(uint256 a, uint256 b) internal constant returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a + b);require(a >= 0);require(b >= 0);
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}

contract BasicToken is ERC20Basic {mapping(address => uint256) old_balances;
  using SafeMath for uint256;

  mapping(address => uint256) balances;

  /**
  * @dev transfer token for a specified address
  * @param _to The address to transfer to.
  * @param _value The amount to be transferred.
  */
  /// ensures(msg.sender != _to && balances[msg.sender] >= _value, balances[msg.sender] == old(balances[msg.sender]) - _value && balances[_to] == old(balances[_to]) + _value)
  function transfer(address _to, uint256 _value) returns (bool) {(bool __v1, bool __v2)=(msg.sender != _to && balances[msg.sender] >= _value,  balances[msg.sender] == old_balances[msg.sender] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
    balances[msg.sender] = balances[msg.sender].sub(_value);
    balances[_to] = balances[_to].add(_value);
    Transfer(msg.sender, _to, _value);
    return true;
  }

  /**
  * @dev Gets the balance of the specified address.
  * @param _owner The address to query the the balance of. 
  * @return An uint256 representing the amount owned by the passed address.
  */
  /// ensures(true, balance == balances[_owner])
  function balanceOf(address _owner) constant returns (uint256 balance) {(bool __v1, bool __v2)=(true,  balance == balances[_owner]);
    return balances[_owner];
  }

}

contract StandardToken is ERC20, BasicToken {mapping(address => mapping(address => uint256)) old_allowed;

  mapping (address => mapping (address => uint256)) allowed;


  /**
   * @dev Transfer tokens from one address to another
   * @param _from address The address which you want to send tokens from
   * @param _to address The address which you want to transfer to
   * @param _value uint256 the amout of tokens to be transfered
   */
  /// ensures(_from != _to && _value <= balances[_from] && _value <= allowed[_from][msg.sender], balances[_from] == old(balances[_from]) - _value && balances[_to] == old(balances[_to]) + _value)
  function transferFrom(address _from, address _to, uint256 _value) returns (bool) {(bool __v1, bool __v2)=(_from != _to && _value <= balances[_from] && _value <= allowed[_from][msg.sender],  balances[_from] == old_balances[_from] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
    var _allowance = allowed[_from][msg.sender];

    // Check is not needed because sub(_allowance, _value) will already throw if this condition is not met
    // require (_value <= _allowance);

    balances[_to] = balances[_to].add(_value);
    balances[_from] = balances[_from].sub(_value);
    allowed[_from][msg.sender] = _allowance.sub(_value);
    Transfer(_from, _to, _value);
    return true;
  }

  /**
   * @dev Aprove the passed address to spend the specified amount of tokens on behalf of msg.sender.
   * @param _spender The address which will spend the funds.
   * @param _value The amount of tokens to be spent.
   */
  /// ensures((_value == 0) || (allowed[msg.sender][_spender] == 0), allowed[msg.sender][_spender] == _value)
  function approve(address _spender, uint256 _value) returns (bool) {(bool __v1, bool __v2)=((_value == 0) || (allowed[msg.sender][_spender] == 0),  allowed[msg.sender][_spender] == _value);require(_value >= 0);

    // To change the approve amount you first have to reduce the addresses`
    //  allowance to zero by calling `approve(_spender, 0)` if it is not
    //  already 0 to mitigate the race condition described here:
    //  https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
    require((_value == 0) || (allowed[msg.sender][_spender] == 0));

    allowed[msg.sender][_spender] = _value;
    Approval(msg.sender, _spender, _value);
    return true;
  }

  /**
   * @dev Function to check the amount of tokens that an owner allowed to a spender.
   * @param _owner address The address which owns the funds.
   * @param _spender address The address which will spend the funds.
   * @return A uint256 specifing the amount of tokens still avaible for the spender.
   */
  /// ensures(true, remaining == allowed[_owner][_spender])
  function allowance(address _owner, address _spender) constant returns (uint256 remaining) {(bool __v1, bool __v2)=(true,  remaining == allowed[_owner][_spender]);
    return allowed[_owner][_spender];
  }

}

contract MintableToken is StandardToken, Ownable {bool old_mintingFinished;
  event Mint(address indexed to, uint256 amount);
  event MintFinished();

  bool public mintingFinished = false;


  modifier canMint() {
    require(!mintingFinished);
    _;
  }

  /**
   * @dev Function to mint tokens
   * @param _to The address that will recieve the minted tokens.
   * @param _amount The amount of tokens to mint.
   * @return A boolean that indicates if the operation was successful.
   */
  /// ensures(msg.sender == owner && !mintingFinished, totalSupply == old(totalSupply) + _amount && balances[_to] == old(balances[_to]) + _amount)
  function mint(address _to, uint256 _amount) onlyOwner canMint returns (bool) {(bool __v1, bool __v2)=(msg.sender == owner && !mintingFinished,  totalSupply == old_totalSupply + _amount && balances[_to] == old_balances[_to] + _amount);require(_amount >= 0);require(totalSupply >= 0);
    totalSupply = totalSupply.add(_amount);
    balances[_to] = balances[_to].add(_amount);
    Mint(_to, _amount);
    return true;
  }

  /**
   * @dev Function to stop minting new tokens.
   * @return True if the operation was successful.
   */
  /// ensures(msg.sender == owner, mintingFinished)
  function finishMinting() onlyOwner returns (bool) {(bool __v1, bool __v2)=(msg.sender == owner,  mintingFinished);
    mintingFinished = true;
    MintFinished();
    return true;
  }
}

contract PausableToken is StandardToken, Pausable {
  /// ensures(!paused && msg.sender != _to && balances[msg.sender] >= _value, true)
  function transfer(address _to, uint _value) whenNotPaused returns (bool) {(bool __v1, bool __v2)=(!paused && msg.sender != _to && balances[msg.sender] >= _value,  true);require(_value >= 0);
    return super.transfer(_to, _value);
  }
  /// ensures(!paused && _from != _to && _value <= balances[_from] && _value <= allowed[_from][msg.sender], true)
  function transferFrom(address _from, address _to, uint _value) whenNotPaused returns (bool) {(bool __v1, bool __v2)=(!paused && _from != _to && _value <= balances[_from] && _value <= allowed[_from][msg.sender],  true);require(_value >= 0);
    return super.transferFrom(_from, _to, _value);
  }
}

contract BurnableToken is StandardToken {

    event Burn(address indexed burner, uint256 value);

    /**
     * @dev Burns a specified amount of tokens.
     * @param _value The amount of tokens to burn. 
     */
    /// ensures(_value > 0 && balances[msg.sender] >= _value && totalSupply >= _value, balances[msg.sender] == old(balances[msg.sender]) - _value && totalSupply == old(totalSupply) - _value)
    function burn(uint256 _value) public {(bool __v1, bool __v2)=(_value > 0 && balances[msg.sender] >= _value && totalSupply >= _value,  balances[msg.sender] == old_balances[msg.sender] - _value && totalSupply == old_totalSupply - _value);require(_value >= 0);require(totalSupply >= 0);
        require(_value > 0);

        address burner = msg.sender;
        balances[burner] = balances[burner].sub(_value);
        totalSupply = totalSupply.sub(_value);
        Burn(msg.sender, _value);
    }

}

contract MANAToken is BurnableToken, PausableToken, MintableToken {string old_symbol;string old_name;uint8 old_decimals;

    string public constant symbol = "MANA";

    string public constant name = "Decentraland MANA";

    uint8 public constant decimals = 18;
    /// ensures(_value > 0 && balances[msg.sender] >= _value && totalSupply >= _value, true)
    function burn(uint256 _value) whenNotPaused public {(bool __v1, bool __v2)=(_value > 0 && balances[msg.sender] >= _value && totalSupply >= _value,  true);require(_value >= 0);
        super.burn(_value);
    }
}