pragma solidity ^0.4.24;

contract ERC20 {
    function totalSupply() public constant returns (uint256);
    function balanceOf(address tokenOwner) public constant returns (uint256);
    function allowance(address tokenOwner, address spender) public constant returns (uint256);
    function transfer(address to, uint tokens) public returns (bool);
    function approve(address spender, uint tokens) public returns (bool);
    function transferFrom(address from, address to, uint tokens) public returns (bool);
    function name() public returns (string);
    function symbol() public returns (string);
    function decimals() public returns (uint8);
    function stopped() public returns (bool);

    event Transfer(address indexed from, address indexed to, uint tokens);
    event Approval(address indexed tokenOwner, address indexed spender, uint tokens);
}

contract ERC20_new {
    mapping(address => uint256) public balances;
    mapping(address => mapping (address => uint256)) public allowed;
    string public name;
    string public symbol;
    uint8 public decimals;
    uint256 public totalSupply;
    address public owner;

    uint256 private constant MAX_UINT256 = 2**256 -1 ;

    mapping(address => bool) private migratedBalances;
    ERC20 private oldToken;

    event Transfer(address indexed _from, address indexed _to, uint _value);
    event Approval(address indexed _tokenOwner, address indexed _spender, uint _value);
    event Migrate(address _acct, uint256 _value);
    event OwnershipTransferred(address _old, address _new);

    constructor(ERC20 oldTokenAddr)
        public
    {
        require(oldTokenAddr.stopped());
        oldToken = oldTokenAddr;
        name = oldToken.name();
        symbol = oldToken.symbol();
        decimals = oldToken.decimals();
        totalSupply = oldToken.totalSupply();
        owner = msg.sender;
    }

    function transferFrom(address from, address to, uint256 value)
        public returns (bool)
    {
        uint256 allowance = allowed[from][msg.sender];

        if (!migratedBalances[from]) {
             uint256 oldValue = oldToken.balanceOf(from);
             balances[from] += oldValue;
             migratedBalances[from] = true;
             emit Migrate(from, oldValue);
        }

        require(balances[from] >= value) ;
        require(allowance >= value) ;

        balances[from] -= value ;
        balances[to] += value;

        if (allowance < MAX_UINT256) {
            allowed[from][msg.sender] -= value;
        }

        emit Transfer(from, to, value) ;
        return true;
    }

    function transfer(address to, uint256 value)
        public returns (bool)
    {
        if (!migratedBalances[msg.sender]) {
            uint256 oldValue = oldToken.balanceOf(msg.sender);
            balances[msg.sender] += oldValue;
            migratedBalances[msg.sender] = true;
            emit Migrate(msg.sender, oldValue);
        }

        require(balances[msg.sender] >= value) ;

        balances[msg.sender] -= value ;
        balances[to] += value ;

        emit Transfer(msg.sender, to, value);
        return true;
    }

    function balanceOf(address addr)
        public returns (uint256)
    {
        if (!migratedBalances[addr]) {
            uint256 oldValue = oldToken.balanceOf(addr);
            balances[addr] += oldValue;
            migratedBalances[addr] = true;
            emit Migrate(addr, oldValue);
        }
        return balances[addr];
    }

    function approve(address spender, uint256 value)
        public returns (bool)
    {
        allowed[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function allowance(address addr, address spender)
        public view returns (uint256)
    {
        return allowed[addr][spender];
    }

    function increaseApproval(address spender, uint256 addValue)
        public returns (bool)
    {
        require(allowed[msg.sender][spender] <= MAX_UINT256 - addValue);
        allowed[msg.sender][spender] += addValue ;
        emit Approval(msg.sender, spender, allowed[msg.sender][spender]) ;
        return true;
    }

    function decreaseApproval(address spender, uint256 subValue)
        public returns (bool)
    {
        uint256 oldValue = allowed[msg.sender][spender] ;
        if (oldValue < subValue) {
            allowed[msg.sender][spender] = 0;
        } else {
            allowed[msg.sender][spender] -= subValue;
        }
        emit Approval(msg.sender, spender, allowed[msg.sender][spender]);
        return true;
    }

    function transferOwnership(address newOwner)
        public returns (bool)
    {
        require(msg.sender == owner);
        owner = newOwner;
        emit OwnershipTransferred(msg.sender, newOwner);
        return true;
    }
}
