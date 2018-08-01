pragma solidity ^0.4.24;

contract ERC20_mintable {
    mapping(address => uint256) public balances;
    mapping(address => mapping (address => uint256)) public allowed;
    string public name;
    string public symbol;
    uint8 public decimals;
    uint256 public totalSupply;

    address private owner;
    bool private mintingFinished;

    uint256 private constant MAX_UINT256 = 2**256 - 1;

    event Transfer(address indexed from, address indexed to, uint tokens);
    event Approval(address indexed tokenOwner, address indexed spender, uint tokens);
    event Mint(address indexed to, uint value);
    event MintFinished();

    constructor(uint256 initialAmount, string tokenName, uint8 decimalUnits, string tokenSymbol)
        public
    {
        balances[msg.sender] = initialAmount;
        totalSupply = initialAmount;
        name = tokenName;
        decimals = decimalUnits;
        symbol = tokenSymbol;
        owner = msg.sender;
        mintingFinished = false;
    }

    function transferFrom(address from, address to, uint256 value )
        public returns (bool)
    {
        uint256 allowance = allowed[from][msg.sender];

        require(balances[from] >= value);
        require(from == to || balances[to] <= MAX_UINT256 - value);
        require(allowance >= value);

        balances[from] -= value;
        balances[to] += value;

        if (allowance < MAX_UINT256) {
            allowed[from][msg.sender] -= value;
        }

        emit Transfer(from, to, value);
        return true;
    }

    function transfer(address to, uint256 value)
        public returns (bool)
    {
        require(balances[msg.sender] >= value);
        require(msg.sender == to || balances[to] <= MAX_UINT256 - value);

        balances[msg.sender] -= value;
        balances[to] += value;

        emit Transfer(msg.sender, to, value);
        return true;
    }

    function balanceOf(address _owner)
        public view returns (uint256)
    {
        return balances[_owner];
    }

    function approve(address spender, uint256 value)
        public returns (bool)
    {
        allowed[msg.sender][spender] = value;
        emit Approval(msg.sender, spender, value);
        return true;
    }

    function allowance(address _owner, address spender)
        public view returns (uint256)
    {
        return allowed[_owner][spender];
    }

    function increaseApproval(address spender, uint256 value)
        public returns (bool)
    {
        require(allowed[msg.sender][spender] <= MAX_UINT256 - value);
        allowed[msg.sender][spender] += value;
        emit Approval(msg.sender, spender, allowed[msg.sender][spender]);
        return true;
    }

    function decreaseApproval(address spender, uint256 value)
        public returns (bool)
    {
        uint256 oldValue = allowed[msg.sender][spender];

        if (oldValue < value) {
            allowed[msg.sender][spender] = 0;
        } else {
            allowed[msg.sender][spender] -= value;
        }

        emit Approval(msg.sender, spender, allowed[msg.sender][spender]);
        return true;
    }

    function mint(address to, uint256 amount)
        public returns (bool)
    {
        require(owner == msg.sender);
        require(!mintingFinished);
        require(totalSupply <= MAX_UINT256 - amount);
        require(balances[to] <= MAX_UINT256 - amount);

        totalSupply += amount;
        balances[to] += amount;

        emit Mint(to, amount);
        emit Transfer(0, to, amount);
        return true;
    }

    function finishMinting()
        public returns (bool)
    {
          require(msg.sender == owner);
          require(!mintingFinished);

          mintingFinished = true;

          emit MintFinished();
          return true;
    }
}
