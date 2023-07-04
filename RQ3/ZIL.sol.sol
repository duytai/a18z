/**
 *Submitted for verification at Etherscan.io on 2018-01-12
*/

// pragma solidity ^0.4.18;

/**
 * @title ERC20Basic
 * @dev Simpler version of ERC20 interface
 * @dev see https://github.com/ethereum/EIPs/issues/179
 */
contract ERC20Basic {uint256 old_totalSupply;
  uint256 public totalSupply;
  function balanceOf(address who) public view returns (uint256);
  function transfer(address to, uint256 value) public returns (bool);
  event Transfer(address indexed from, address indexed to, uint256 value);
}

/**
 * @title ERC20 interface
 * @dev see https://github.com/ethereum/EIPs/issues/20
 */
contract ERC20 is ERC20Basic {
  function allowance(address owner, address spender) public view returns (uint256);
  function transferFrom(address from, address to, uint256 value) public returns (bool);
  function approve(address spender, uint256 value) public returns (bool);
  event Approval(address indexed owner, address indexed spender, uint256 value);
}


/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {
  /// ensures(true, r == a * b)
  function mul(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a * b);require(a >= 0);require(b >= 0);
    if (a == 0) {
      return 0;
    }
    uint256 c = a * b;
    // assert(c / a == b);
    return c;
  }
  /// ensures(true, r == a / b)
  function div(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a / b);require(a >= 0);require(b >= 0);
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return c;
  }
  /// ensures(a >= b, r == a - b)
  function sub(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(a >= b,  r == a - b);require(a >= 0);require(b >= 0);
    assert(b <= a);
    return a - b;
  }
  /// ensures(true, r == a + b)
  function add(uint256 a, uint256 b) internal pure returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == a + b);require(a >= 0);require(b >= 0);
    uint256 c = a + b;
    assert(c >= a);
    return c;
  }
}


/**
 * @title Basic token
 * @dev Basic version of StandardToken, with no allowances.
 */
contract BasicToken is ERC20Basic {mapping(address => uint256) old_balances;
  using SafeMath for uint256;

  mapping(address => uint256) balances;

  /**
  * @dev transfer token for a specified address
  * @param _to The address to transfer to.
  * @param _value The amount to be transferred.
  */
  /// ensures(msg.sender != _to && _to != address(0) && _value <= balances[msg.sender], balances[msg.sender] == old(balances[msg.sender]) - _value && balances[_to] == old(balances[_to]) + _value)
  function transfer(address _to, uint256 _value) public returns (bool) {(bool __v1, bool __v2)=(msg.sender != _to && _to != address(0) && _value <= balances[msg.sender],  balances[msg.sender] == old_balances[msg.sender] - _value && balances[_to] == old_balances[_to] + _value);require(_value >= 0);
    require(_to != address(0));
    require(_value <= balances[msg.sender]);

    // SafeMath.sub will throw if there is not enough balance.
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
  function balanceOf(address _owner) public view returns (uint256 balance) {(bool __v1, bool __v2)=(true,  balance == balances[_owner]);
    return balances[_owner];
  }

}

/**
 * @title Standard ERC20 token
 *
 * @dev Implementation of the basic standard token.
 * @dev https://github.com/ethereum/EIPs/issues/20
 * @dev Based on code by FirstBlood: https://github.com/Firstbloodio/token/blob/master/smart_contract/FirstBloodToken.sol
 */
contract StandardToken is ERC20, BasicToken {mapping(address => mapping(address => uint256)) old_allowed;

  mapping (address => mapping (address => uint256)) internal allowed;


  /**
   * @dev Transfer tokens from one address to another
   * @param _from address The address which you want to send tokens from
   * @param _to address The address which you want to transfer to
   * @param _value uint256 the amount of tokens to be transferred
   */
  /// ensures(_from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender], balances[_from] == old(balances[_from]) - _value && balances[_to] == old(balances[_to]) + _value && allowed[_from][msg.sender] == old(allowed[_from][msg.sender]) - _value && r)
  function transferFrom(address _from, address _to, uint256 _value) public returns (bool r) {(bool __v1, bool __v2)=(_from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender],  balances[_from] == old_balances[_from] - _value && balances[_to] == old_balances[_to] + _value && allowed[_from][msg.sender] == old_allowed[_from][msg.sender] - _value && r);require(_value >= 0);
    require(_to != address(0));
    require(_value <= balances[_from]);
    require(_value <= allowed[_from][msg.sender]);

    balances[_from] = balances[_from].sub(_value);
    balances[_to] = balances[_to].add(_value);
    allowed[_from][msg.sender] = allowed[_from][msg.sender].sub(_value);
    Transfer(_from, _to, _value);
    return true;
  }

  /**
   * @dev Approve the passed address to spend the specified amount of tokens on behalf of msg.sender.
   *
   * Beware that changing an allowance with this method brings the risk that someone may use both the old
   * and the new allowance by unfortunate transaction ordering. One possible solution to mitigate this
   * race condition is to first reduce the spender's allowance to 0 and set the desired value afterwards:
   * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
   * @param _spender The address which will spend the funds.
   * @param _value The amount of tokens to be spent.
   */
  /// ensures(true, allowed[msg.sender][_spender] == _value)
  function approve(address _spender, uint256 _value) public returns (bool) {(bool __v1, bool __v2)=(true,  allowed[msg.sender][_spender] == _value);require(_value >= 0);
    allowed[msg.sender][_spender] = _value;
    Approval(msg.sender, _spender, _value);
    return true;
  }

  /**
   * @dev Function to check the amount of tokens that an owner allowed to a spender.
   * @param _owner address The address which owns the funds.
   * @param _spender address The address which will spend the funds.
   * @return A uint256 specifying the amount of tokens still available for the spender.
   */
  /// ensures(true, r == allowed[_owner][_spender])
  function allowance(address _owner, address _spender) public view returns (uint256 r) {(bool __v1, bool __v2)=(true,  r == allowed[_owner][_spender]);
    return allowed[_owner][_spender];
  }

  /**
   * approve should be called when allowed[_spender] == 0. To increment
   * allowed value is better to use this function to avoid 2 calls (and wait until
   * the first transaction is mined)
   * From MonolithDAO Token.sol
   */
  /// ensures(true, allowed[msg.sender][_spender] == old(allowed[msg.sender][_spender]) + _addedValue)
  function increaseApproval(address _spender, uint _addedValue) public returns (bool) {(bool __v1, bool __v2)=(true,  allowed[msg.sender][_spender] == old_allowed[msg.sender][_spender] + _addedValue);require(_addedValue >= 0);
    allowed[msg.sender][_spender] = allowed[msg.sender][_spender].add(_addedValue);
    Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }
  /// ensures(_subtractedValue <= allowed[msg.sender][_spender], allowed[msg.sender][_spender] == old(allowed[msg.sender][_spender]) - _subtractedValue)
  function decreaseApproval(address _spender, uint _subtractedValue) public returns (bool) {(bool __v1, bool __v2)=(_subtractedValue <= allowed[msg.sender][_spender],  allowed[msg.sender][_spender] == old_allowed[msg.sender][_spender] - _subtractedValue);require(_subtractedValue >= 0);
    uint oldValue = allowed[msg.sender][_spender];
    if (_subtractedValue > oldValue) {
      allowed[msg.sender][_spender] = 0;
    } else {
      allowed[msg.sender][_spender] = oldValue.sub(_subtractedValue);
    }
    Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }

}

/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {address old_owner;
  address public owner;


  event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);


  /**
   * @dev The Ownable constructor sets the original `owner` of the contract to the sender
   * account.
   */
  /// ensures(true, owner == msg.sender)
  function Ownable() public {(bool __v1, bool __v2)=(true,  owner == msg.sender);
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
  function transferOwnership(address newOwner) public onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner && newOwner != address(0),  owner == newOwner);
    require(newOwner != address(0));
    OwnershipTransferred(owner, newOwner);
    owner = newOwner;
  }

}

/**
 * @title Pausable
 * @dev Base contract which allows children to implement an emergency stop mechanism.
 */
contract Pausable is Ownable {bool old_pausedPublic;bool old_pausedOwnerAdmin;address old_admin;
  event PausePublic(bool newState);
  event PauseOwnerAdmin(bool newState);

  bool public pausedPublic = true;
  bool public pausedOwnerAdmin = false;

  address public admin;

  /**
   * @dev Modifier to make a function callable based on pause states.
   */
  modifier whenNotPaused() {
    if(pausedPublic) {
      if(!pausedOwnerAdmin) {
        require(msg.sender == admin || msg.sender == owner);
      } else {
        revert();
      }
    }
    _;
  }

  /**
   * @dev called by the owner to set new pause flags
   * pausedPublic can't be false while pausedOwnerAdmin is true
   */
  /// ensures(msg.sender == owner && !(newPausedPublic == false && newPausedOwnerAdmin == true), pausedPublic == newPausedPublic && pausedOwnerAdmin == newPausedOwnerAdmin)
  function pause(bool newPausedPublic, bool newPausedOwnerAdmin) onlyOwner public {(bool __v1, bool __v2)=(msg.sender == owner && !(newPausedPublic == false && newPausedOwnerAdmin == true),  pausedPublic == newPausedPublic && pausedOwnerAdmin == newPausedOwnerAdmin);
    require(!(newPausedPublic == false && newPausedOwnerAdmin == true));

    pausedPublic = newPausedPublic;
    pausedOwnerAdmin = newPausedOwnerAdmin;

    PausePublic(newPausedPublic);
    PauseOwnerAdmin(newPausedOwnerAdmin);
  }
}

contract PausableToken is StandardToken, Pausable {
  /// ensures(!pausedPublic && msg.sender != _to && _to != address(0) && _value <= balances[msg.sender], true)
  function transfer(address _to, uint256 _value) public whenNotPaused returns (bool) {(bool __v1, bool __v2)=(!pausedPublic && msg.sender != _to && _to != address(0) && _value <= balances[msg.sender],  true);require(_value >= 0);
    return super.transfer(_to, _value);
  }
  /// ensures(!pausedPublic && _from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender], r)
  function transferFrom(address _from, address _to, uint256 _value) public whenNotPaused returns (bool r) {(bool __v1, bool __v2)=(!pausedPublic && _from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender],  r);require(_value >= 0);
    return super.transferFrom(_from, _to, _value);
  }
  /// ensures(!pausedPublic, true)
  function approve(address _spender, uint256 _value) public whenNotPaused returns (bool) {(bool __v1, bool __v2)=(!pausedPublic,  true);require(_value >= 0);
    return super.approve(_spender, _value);
  }
  /// ensures(!pausedPublic, true)
  function increaseApproval(address _spender, uint _addedValue) public whenNotPaused returns (bool success) {(bool __v1, bool __v2)=(!pausedPublic,  true);require(_addedValue >= 0);
    return super.increaseApproval(_spender, _addedValue);
  }
  /// ensures(!pausedPublic && _subtractedValue <= allowed[msg.sender][_spender], true)
  function decreaseApproval(address _spender, uint _subtractedValue) public whenNotPaused returns (bool success) {(bool __v1, bool __v2)=(!pausedPublic && _subtractedValue <= allowed[msg.sender][_spender],  true);require(_subtractedValue >= 0);
    return super.decreaseApproval(_spender, _subtractedValue);
  }
}


contract ZilliqaToken is PausableToken {string old_name;string old_symbol;uint8 old_decimals;
    string  public  constant name = "Zilliqa";
    string  public  constant symbol = "ZIL";
    uint8   public  constant decimals = 12;

    modifier validDestination( address to )
    {
        require(to != address(0x0));
        require(to != address(this));
        _;
    }
    /// ensures(true, admin == _admin && totalSupply == _totalTokenAmount && balances[msg.sender] == _totalTokenAmount)
    function ZilliqaToken( address _admin, uint _totalTokenAmount ) 
    {(bool __v1, bool __v2)=(true,  admin == _admin && totalSupply == _totalTokenAmount && balances[msg.sender] == _totalTokenAmount);require(_totalTokenAmount >= 0);
        // assign the admin account
        admin = _admin;

        // assign the total tokens to zilliqa
        totalSupply = _totalTokenAmount;
        balances[msg.sender] = _totalTokenAmount;
        Transfer(address(0x0), msg.sender, _totalTokenAmount);
    }
    /// ensures(!pausedPublic && _to != address(this) && msg.sender != _to && _to != address(0) && _value <= balances[msg.sender], true)
    function transfer(address _to, uint _value) validDestination(_to) returns (bool) 
    {(bool __v1, bool __v2)=(!pausedPublic && _to != address(this) && msg.sender != _to && _to != address(0) && _value <= balances[msg.sender],  true);require(_value >= 0);
        return super.transfer(_to, _value);
    }
    /// ensures(!pausedPublic && _to != address(this) && _from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender], r)
    function transferFrom(address _from, address _to, uint _value) validDestination(_to) returns (bool r) 
    {(bool __v1, bool __v2)=(!pausedPublic && _to != address(this) && _from != _to && _to != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender],  r);require(_value >= 0);
        return super.transferFrom(_from, _to, _value);
    }

    event Burn(address indexed _burner, uint _value);
    /// ensures(balances[msg.sender] >= _value && totalSupply >= _value, balances[msg.sender] == old(balances[msg.sender]) - _value && totalSupply == old(totalSupply) - _value)
    function burn(uint _value) returns (bool)
    {(bool __v1, bool __v2)=(balances[msg.sender] >= _value && totalSupply >= _value,  balances[msg.sender] == old_balances[msg.sender] - _value && totalSupply == old_totalSupply - _value);require(_value >= 0);require(totalSupply >= 0);
        balances[msg.sender] = balances[msg.sender].sub(_value);
        totalSupply = totalSupply.sub(_value);
        Burn(msg.sender, _value);
        Transfer(msg.sender, address(0x0), _value);
        return true;
    }

    // save some gas by making only one contract call
    /// ensures(!pausedPublic && msg.sender != address(this) && _from != msg.sender && msg.sender != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender] && balances[msg.sender] >= _value && totalSupply >= _value, true)
    function burnFrom(address _from, uint256 _value) returns (bool) 
    {(bool __v1, bool __v2)=(!pausedPublic && msg.sender != address(this) && _from != msg.sender && msg.sender != address(0) && _value <= balances[_from] && _value <= allowed[_from][msg.sender] && balances[msg.sender] >= _value && totalSupply >= _value,  true);require(_value >= 0);
        assert( transferFrom( _from, msg.sender, _value ) );
        return burn(_value);
    }
    /// ensures(msg.sender == owner, true)
    function emergencyERC20Drain( ERC20 token, uint amount ) onlyOwner {(bool __v1, bool __v2)=(msg.sender == owner,  true);require(amount >= 0);
        // owner can drain tokens that are sent here by mistake
        token.transfer( owner, amount );
    }

    event AdminTransferred(address indexed previousAdmin, address indexed newAdmin);
    /// ensures(true, admin == newAdmin)
    function changeAdmin(address newAdmin) onlyOwner {(bool __v1, bool __v2)=(true,  admin == newAdmin);
        // owner can re-assign the admin
        AdminTransferred(admin, newAdmin);
        admin = newAdmin;
    }
}