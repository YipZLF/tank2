// Tank2 游戏样例程序
// 随机策略
// 作者：289371298 upgraded from zhouhy
// https://www.botzone.org.cn/games/Tank2

#include <cstring>
#include <ctime>
#include <iostream>
#include <queue>
#include <set>
#include <stack>
#include <string>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include "jsoncpp/json.h"
#endif

//#define DEBUG

using std::cin;
using std::cout;
using std::deque;
using std::endl;
using std::flush;
using std::getline;
using std::make_pair;
using std::pair;
using std::queue;
using std::set;
using std::string;
using std::vector;

namespace TankGame
{
using std::istream;
using std::set;
using std::stack;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

enum GameResult
{
    NotFinished = -2,
    Draw = -1,
    Blue = 0,
    Red = 1
};

enum FieldItem
{
    None = 0,
    Brick = 1,
    Steel = 2,
    Base = 4,
    Blue0 = 8,
    Blue1 = 16,
    Red0 = 32,
    Red1 = 64,
    Water = 128
};

template <typename T>
inline T operator~(T a) { return (T) ~(int)a; }
template <typename T>
inline T operator|(T a, T b) { return (T)((int)a | (int)b); }
template <typename T>
inline T operator&(T a, T b) { return (T)((int)a & (int)b); }
template <typename T>
inline T operator^(T a, T b) { return (T)((int)a ^ (int)b); }
template <typename T>
inline T &operator|=(T &a, T b) { return (T &)((int &)a |= (int)b); }
template <typename T>
inline T &operator&=(T &a, T b) { return (T &)((int &)a &= (int)b); }
template <typename T>
inline T &operator^=(T &a, T b) { return (T &)((int &)a ^= (int)b); }

enum Action
{
    Invalid = -2,
    Stay = -1,
    Up,
    Right,
    Down,
    Left,
    UpShoot,
    RightShoot,
    DownShoot,
    LeftShoot
};

// 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
// Side（对战双方） - 0 为蓝，1 为红
// Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
// Turn（回合编号） - 从 1 开始

const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

// 基地的横坐标
const int baseX[sideCount] = {fieldWidth / 2, fieldWidth / 2};

// 基地的纵坐标
const int baseY[sideCount] = {0, fieldHeight - 1};

const int dx[4] = {0, 1, 0, -1}, dy[4] = {-1, 0, 1, 0};
const FieldItem tankItemTypes[sideCount][tankPerSide] = {
    {Blue0, Blue1}, {Red0, Red1}};

int maxTurn = 100;

#ifdef _MSC_VER
#pragma endregion

#pragma region 工具函数和类
#endif

inline bool ActionIsMove(Action x)
{
    return x >= Up && x <= Left;
}

inline bool ActionIsShoot(Action x)
{
    return x >= UpShoot && x <= LeftShoot;
}

inline bool ActionDirectionIsOpposite(Action a, Action b)
{
    return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
}

inline bool CoordValid(int x, int y)
{
    return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
}

// 判断 item 是不是叠在一起的多个坦克
inline bool HasMultipleTank(FieldItem item)
{
    // 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
    // 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
    return !!(item & (item - 1));
}

inline int GetTankSide(FieldItem item)
{
    return item == Blue0 || item == Blue1 ? Blue : Red;
}

inline int GetTankID(FieldItem item)
{
    return item == Blue0 || item == Red0 ? 0 : 1;
}

// 获得动作的方向
inline int ExtractDirectionFromAction(Action x)
{
    if (x >= Up)
        return x % 4;
    return -1;
}

// 物件消失的记录，用于回退
struct DisappearLog
{
    FieldItem item;

    // 导致其消失的回合的编号
    int turn;

    int x, y;
    bool operator<(const DisappearLog &b) const
    {
        if (x == b.x)
        {
            if (y == b.y)
                return item < b.item;
            return y < b.y;
        }
        return x < b.x;
    }
};

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField 主要逻辑类
#endif

class TankField
{
public:
    //!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

    // 游戏场地上的物件（一个格子上可能有多个坦克）
    FieldItem gameField[fieldHeight][fieldWidth] = {};

    // 坦克是否存活
    bool tankAlive[sideCount][tankPerSide] = {{true, true}, {true, true}};

    // 基地是否存活
    bool baseAlive[sideCount] = {true, true};

    // 坦克横坐标，-1表示坦克已炸
    int tankX[sideCount][tankPerSide] = {
        {fieldWidth / 2 - 2, fieldWidth / 2 + 2}, {fieldWidth / 2 + 2, fieldWidth / 2 - 2}};

    // 坦克纵坐标，-1表示坦克已炸
    int tankY[sideCount][tankPerSide] = {{0, 0}, {fieldHeight - 1, fieldHeight - 1}};

    // 当前回合编号
    int currentTurn = 1;

    // 我是哪一方
    int mySide;

    // 用于回退的log
    stack<DisappearLog> logs;

    // 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
    Action previousActions[101][sideCount][tankPerSide] = {{{Stay, Stay}, {Stay, Stay}}};

    //!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

    // 本回合双方即将执行的动作，需要手动填入
    Action nextAction[sideCount][tankPerSide] = {{Invalid, Invalid}, {Invalid, Invalid}};

    // 判断行为是否合法（出界或移动到非空格子算作非法）
    // 未考虑坦克是否存活
    bool ActionIsValid(int side, int tank, Action act)
    {
        if (act == Invalid)
            return false;
        if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
            return false;
        if (act == Stay || act > Left)
            return true;
        int x = tankX[side][tank] + dx[act],
            y = tankY[side][tank] + dy[act];
        return CoordValid(x, y) && gameField[y][x] == None; // water cannot be stepped on
    }

    // 判断 nextAction 中的所有行为是否都合法
    // 忽略掉未存活的坦克
    bool ActionIsValid()
    {
        for (int side = 0; side < sideCount; side++)
            for (int tank = 0; tank < tankPerSide; tank++)
                if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
                    return false;
        return true;
    }

private:
    void _destroyTank(int side, int tank)
    {
        tankAlive[side][tank] = false;
        tankX[side][tank] = tankY[side][tank] = -1;
    }

    void _revertTank(int side, int tank, DisappearLog &log)
    {
        int &currX = tankX[side][tank], &currY = tankY[side][tank];
        if (tankAlive[side][tank])
            gameField[currY][currX] &= ~tankItemTypes[side][tank];
        else
            tankAlive[side][tank] = true;
        currX = log.x;
        currY = log.y;
        gameField[currY][currX] |= tankItemTypes[side][tank];
    }

public:
    // 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
    bool DoAction()
    {
        if (!ActionIsValid())
            return false;

        // 1 移动
        for (int side = 0; side < sideCount; side++)
            for (int tank = 0; tank < tankPerSide; tank++)
            {
                Action act = nextAction[side][tank];

                // 保存动作
                previousActions[currentTurn][side][tank] = act;
                if (tankAlive[side][tank] && ActionIsMove(act))
                {
                    int &x = tankX[side][tank], &y = tankY[side][tank];
                    FieldItem &items = gameField[y][x];

                    // 记录 Log
                    DisappearLog log;
                    log.x = x;
                    log.y = y;
                    log.item = tankItemTypes[side][tank];
                    log.turn = currentTurn;
                    logs.push(log);

                    // 变更坐标
                    x += dx[act];
                    y += dy[act];

                    // 更换标记（注意格子可能有多个坦克）
                    gameField[y][x] |= log.item;
                    items &= ~log.item;
                }
            }

        // 2 射♂击!
        set<DisappearLog> itemsToBeDestroyed;
        for (int side = 0; side < sideCount; side++)
            for (int tank = 0; tank < tankPerSide; tank++)
            {
                Action act = nextAction[side][tank];
                if (tankAlive[side][tank] && ActionIsShoot(act))
                {
                    int dir = ExtractDirectionFromAction(act);
                    int x = tankX[side][tank], y = tankY[side][tank];
                    bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
                    while (true)
                    {
                        x += dx[dir];
                        y += dy[dir];
                        if (!CoordValid(x, y))
                            break;
                        FieldItem items = gameField[y][x];
                        //tank will not be on water, and water will not be shot, so it can be handled as None
                        if (items != None && items != Water)
                        {
                            // 对射判断
                            if (items >= Blue0 &&
                                !hasMultipleTankWithMe && !HasMultipleTank(items))
                            {
                                // 自己这里和射到的目标格子都只有一个坦克
                                Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
                                if (ActionIsShoot(theirAction) &&
                                    ActionDirectionIsOpposite(act, theirAction))
                                {
                                    // 而且我方和对方的射击方向是反的
                                    // 那么就忽视这次射击
                                    break;
                                }
                            }

                            // 标记这些物件要被摧毁了（防止重复摧毁）
                            for (int mask = 1; mask <= Red1; mask <<= 1)
                                if (items & mask)
                                {
                                    DisappearLog log;
                                    log.x = x;
                                    log.y = y;
                                    log.item = (FieldItem)mask;
                                    log.turn = currentTurn;
                                    itemsToBeDestroyed.insert(log);
                                }
                            break;
                        }
                    }
                }
            }

        for (auto &log : itemsToBeDestroyed)
        {
            switch (log.item)
            {
            case Base:
            {
                int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                baseAlive[side] = false;
                break;
            }
            case Blue0:
                _destroyTank(Blue, 0);
                break;
            case Blue1:
                _destroyTank(Blue, 1);
                break;
            case Red0:
                _destroyTank(Red, 0);
                break;
            case Red1:
                _destroyTank(Red, 1);
                break;
            case Steel:
                continue;
            default:;
            }
            gameField[log.y][log.x] &= ~log.item;
            logs.push(log);
        }

        for (int side = 0; side < sideCount; side++)
            for (int tank = 0; tank < tankPerSide; tank++)
                nextAction[side][tank] = Invalid;

        currentTurn++;
        return true;
    }

    // 回到上一回合
    bool Revert()
    {
        if (currentTurn == 1)
            return false;

        currentTurn--;
        while (!logs.empty())
        {
            DisappearLog &log = logs.top();
            if (log.turn == currentTurn)
            {
                logs.pop();
                switch (log.item)
                {
                case Base:
                {
                    int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                    baseAlive[side] = true;
                    gameField[log.y][log.x] = Base;
                    break;
                }
                case Brick:
                    gameField[log.y][log.x] = Brick;
                    break;
                case Blue0:
                    _revertTank(Blue, 0, log);
                    break;
                case Blue1:
                    _revertTank(Blue, 1, log);
                    break;
                case Red0:
                    _revertTank(Red, 0, log);
                    break;
                case Red1:
                    _revertTank(Red, 1, log);
                    break;
                default:;
                }
            }
            else
                break;
        }
        return true;
    }

    // 游戏是否结束？谁赢了？
    GameResult GetGameResult()
    {
        bool fail[sideCount] = {};
        for (int side = 0; side < sideCount; side++)
            if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
                fail[side] = true;
        if (fail[0] == fail[1])
            return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
        if (fail[Blue])
            return Red;
        return Blue;
    }

    /* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
           initialize gameField[][]
           brick>water>steel
        */
    TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide)
    {
        for (int i = 0; i < 3; i++)
        {
            int mask = 1;
            for (int y = i * 3; y < (i + 1) * 3; y++)
            {
                for (int x = 0; x < fieldWidth; x++)
                {
                    if (hasBrick[i] & mask)
                        gameField[y][x] = Brick;
                    else if (hasWater[i] & mask)
                        gameField[y][x] = Water;
                    else if (hasSteel[i] & mask)
                        gameField[y][x] = Steel;
                    mask <<= 1;
                }
            }
        }
        for (int side = 0; side < sideCount; side++)
        {
            for (int tank = 0; tank < tankPerSide; tank++)
                gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
            gameField[baseY[side]][baseX[side]] = Base;
        }
    }
    // 打印场地
    void DebugPrint()
    {
#ifndef _BOTZONE_ONLINE
        const string side2String[] = {"蓝", "红"};
        const string boolean2String[] = {"已炸", "存活"};
        const char *boldHR = "==============================";
        const char *slimHR = "------------------------------";
        cout << boldHR << endl
             << "图例：" << endl
             << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
             << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
             << slimHR << endl;
        for (int y = 0; y < fieldHeight; y++)
        {
            for (int x = 0; x < fieldWidth; x++)
            {
                switch (gameField[y][x])
                {
                case None:
                    cout << '.';
                    break;
                case Brick:
                    cout << '#';
                    break;
                case Steel:
                    cout << '%';
                    break;
                case Base:
                    cout << '*';
                    break;
                case Blue0:
                    cout << 'b';
                    break;
                case Blue1:
                    cout << 'B';
                    break;
                case Red0:
                    cout << 'r';
                    break;
                case Red1:
                    cout << 'R';
                    break;
                case Water:
                    cout << 'W';
                    break;
                default:
                    cout << '@';
                    break;
                }
            }
            cout << endl;
        }
        cout << slimHR << endl;
        for (int side = 0; side < sideCount; side++)
        {
            cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
            for (int tank = 0; tank < tankPerSide; tank++)
                cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
            cout << endl;
        }
        cout << "当前回合：" << currentTurn << "，";
        GameResult result = GetGameResult();
        if (result == -2)
            cout << "游戏尚未结束" << endl;
        else if (result == -1)
            cout << "游戏平局" << endl;
        else
            cout << side2String[result] << "方胜利" << endl;
        cout << boldHR << endl;
#endif
    }

    bool operator!=(const TankField &b) const
    {

        for (int y = 0; y < fieldHeight; y++)
            for (int x = 0; x < fieldWidth; x++)
                if (gameField[y][x] != b.gameField[y][x])
                    return true;

        for (int side = 0; side < sideCount; side++)
            for (int tank = 0; tank < tankPerSide; tank++)
            {
                if (tankX[side][tank] != b.tankX[side][tank])
                    return true;
                if (tankY[side][tank] != b.tankY[side][tank])
                    return true;
                if (tankAlive[side][tank] != b.tankAlive[side][tank])
                    return true;
            }

        if (baseAlive[0] != b.baseAlive[0] ||
            baseAlive[1] != b.baseAlive[1])
            return true;

        if (currentTurn != b.currentTurn)
            return true;

        return false;
    }
};

#ifdef _MSC_VER
#pragma endregion
#endif

TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

// 内部函数
namespace Internals
{
Json::Reader reader;
#ifdef _BOTZONE_ONLINE
Json::FastWriter writer;
#else
Json::StyledWriter writer;
#endif

void _processRequestOrResponse(Json::Value &value, bool isOpponent)
{
    if (value.isArray())
    {
        if (!isOpponent)
        {
            for (int tank = 0; tank < tankPerSide; tank++)
                field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
        }
        else
        {
            for (int tank = 0; tank < tankPerSide; tank++)
                field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
            field->DoAction();
        }
    }
    else
    {
        // 是第一回合，裁判在介绍场地
        int hasBrick[3], hasWater[3], hasSteel[3];
        for (int i = 0; i < 3; i++)
        { //Tank2 feature(???????????????)
            hasWater[i] = value["waterfield"][i].asInt();
            hasBrick[i] = value["brickfield"][i].asInt();
            hasSteel[i] = value["steelfield"][i].asInt();
        }
        field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
    }
}

// 请使用 SubmitAndExit 或者 SubmitAndDontExit
void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
{
    Json::Value output(Json::objectValue), response(Json::arrayValue);
    response[0U] = tank0;
    response[1U] = tank1;
    output["response"] = response;
    if (!debug.empty())
        output["debug"] = debug;
    if (!data.empty())
        output["data"] = data;
    if (!globalData.empty())
        output["globalData"] = globalData;
    cout << writer.write(output) << endl;
}
} // namespace Internals

// 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
// 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
void ReadInput(istream &in, string &outData, string &outGlobalData)
{
    Json::Value input;
    string inputString;
    do
    {
        getline(in, inputString);
    } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
    // 猜测是单行还是多行
    char lastChar = inputString[inputString.size() - 1];
    if (lastChar != '}' && lastChar != ']')
    {
        // 第一行不以}或]结尾，猜测是多行
        string newString;
        do
        {
            getline(in, newString);
            inputString += newString;
        } while (newString != "}" && newString != "]");
    }
#endif
    Internals::reader.parse(inputString, input);

    if (input.isObject())
    {
        Json::Value requests = input["requests"], responses = input["responses"];
        if (!requests.isNull() && requests.isArray())
        {
            size_t n = requests.size();
            int i;
            for (i = 0; i < n; i++)
            {
                Internals::_processRequestOrResponse(requests[i], true);
                if (i < n - 1)
                    Internals::_processRequestOrResponse(responses[i], false);
            }
            outData = input["data"].asString();
            outGlobalData = input["globaldata"].asString();
            return;
        }
    }
    Internals::_processRequestOrResponse(input, true);
}

void ReadInput_longlive(istream &in)
{
    Json::Value input;
    string inputString;
    do
    {
        getline(in, inputString);
    } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
    // 猜测是单行还是多行
    char lastChar = inputString[inputString.size() - 1];
    if (lastChar != '}' && lastChar != ']')
    {
        // 第一行不以}或]结尾，猜测是多行
        string newString;
        do
        {
            getline(in, newString);
            inputString += newString;
        } while (newString != "}" && newString != "]");
    }
#endif
    Internals::reader.parse(inputString, input);
#ifdef DEBUG
    cout << "LongLive" << endl;
#endif
    if (input.isObject())
    {
        Json::Value requests = input["requests"];

        size_t n = requests.size();
#ifdef DEBUG
        cout << "request size:" << n << endl;
        cout << "request :" << requests[0] << endl;
#endif
        int i;
        for (i = 0; i < n; i++)
        {
            Internals::_processRequestOrResponse(requests[i], true);
        }
        return;
    }
    Internals::_processRequestOrResponse(input, true);
}

// 提交决策并退出，下回合时会重新运行程序
void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
{
    Internals::_submitAction(tank0, tank1, debug, data, globalData);
    exit(0);
}

// 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
// 如果游戏结束，程序会被系统杀死
void SubmitAndDontExit(Action tank0, Action tank1)
{
    Internals::_submitAction(tank0, tank1);
    field->nextAction[field->mySide][0] = tank0;
    field->nextAction[field->mySide][1] = tank1;
    cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
}
#ifdef _MSC_VER
#pragma endregion
#endif
} // namespace TankGame

namespace TankGame
{

/*RandAction*/
int RandBetween(int from, int to)
{
    return rand() % (to - from) + from;
}

Action RandAction(int tank)
{
    while (true)
    {
        auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
        if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
            return act;
    }
}

Action RandActionExcept(int tank, Action exc)
{
    while (true)
    {
        Action act = RandAction(tank);
        if (act != exc)
            return act;
    }
}

enum AgentState
{
    EXPLORE = 1,
    ATTACK = 2,
    DEFEND = 3
};

#define TANK_CNT 2
#define INF 0x7fffffff
#include <set>

class HeadQuarter
{
public:
    AgentState cur_state[TANK_CNT];
    int mySide, otherSide;
    bool has_shoot[TANK_CNT];

    // Take action
    Action takeAction(int tank_id);
    // State transition happens here.
    bool changeState(int tank_id);

    // EXPLORE
    Action Explore(int tank_id);
    // for A* algorithm, f = g(real) + h(estimate)
    bool first_move[TANK_CNT];
    void A_search(int tank_id, int dst_x, int dst_y);
    int getEstimateScore(int x, int y, int dst_x, int dst_y);
    int g_score[TANK_CNT][fieldHeight][fieldWidth];
    int h_score[TANK_CNT][fieldHeight][fieldWidth];
    int pfather[TANK_CNT][fieldHeight][fieldWidth];
    deque<int> next_loc_x[TANK_CNT];
    deque<int> next_loc_y[TANK_CNT];

    // Attack
    Action Attack(int tank_id);
    Action inShootRange(int tank_id, int e_tank_id);
    // aim[i] marks the idx of the enemy tank that
    // tank i of our side aims at
    vector<int> aim[TANK_CNT];

    // Defend
    Action Defend(int tank_id);

    HeadQuarter()
    {
        cur_state[0] = EXPLORE;
        cur_state[1] = EXPLORE;
        first_move[0] = true;
        first_move[1] = true;
        has_shoot[0] = false;
        has_shoot[1] = false;
    }

private:
    int getManhattenDist(int x, int y, int dst_x, int dst_y)
    {
        return abs(dst_x - x) + abs(dst_y - y);
    }
};

bool HeadQuarter::changeState(int tank_id)
{
    int dist1, dist2;
    int i = tank_id;
    // change to attack: if enemy tank is close
    dist1 = getManhattenDist(field->tankX[mySide][i], field->tankY[mySide][i],
                             field->tankX[otherSide][0], field->tankY[otherSide][0]);
    dist2 = getManhattenDist(field->tankX[mySide][i], field->tankY[mySide][i],
                             field->tankX[otherSide][1], field->tankY[otherSide][1]);
    if (dist2 <= 2 || dist1 <= 2)
    {
        aim[i].push_back(((dist1 < dist2) ? 0 : 1));
        cur_state[i] = ATTACK;
        return true;
    }

    // defend: if enemy tank is close to our base
    dist1 = getManhattenDist(baseX[mySide], baseY[mySide],
                             field->tankX[otherSide][0], field->tankY[otherSide][0]);
    dist2 = getManhattenDist(baseX[mySide], baseY[mySide],
                             field->tankX[otherSide][1], field->tankY[otherSide][1]);
    if (dist2 <= 2 || dist1 <= 2)
    {
        aim[i].push_back(((dist1 < dist2) ? 0 : 1));
        cur_state[i] = DEFEND;
        return true;
    }

    // back to explore: if enemy tank is destroyed
    if ((cur_state[i] == DEFEND || cur_state[i] == ATTACK) &&
        field->tankX[otherSide][aim[i][0]] == -1)
    {
        ///??? 为啥用vector
        aim[i].erase(aim[i].begin());
        cur_state[i] = EXPLORE;
    }
    return true;
}

Action HeadQuarter::takeAction(int tank_id)
{
#ifdef DEBUG
    cout << "cur state of " << tank_id << " is " << cur_state[tank_id] << endl;
#endif
#ifdef DEBUG
    cout << "Shot state of " << tank_id << " is " << has_shoot[tank_id] << endl;
#endif
    changeState(tank_id);
    if (!field->tankAlive[mySide][tank_id])
        return Stay;
    Action to_take;
    switch (cur_state[tank_id])
    {
    case EXPLORE:
        to_take = Explore(tank_id);
        break;
    case ATTACK:
        to_take = Attack(tank_id);
        break;
    case DEFEND:
        to_take = Defend(tank_id);
        break;
    default:
        to_take = Stay;
        break;
    }

    // Shooting twice is prohibited.
    if (!ActionIsShoot(to_take))
        has_shoot[tank_id] = false;
    else
    {
        if (has_shoot[tank_id])
        {
            to_take = Stay;
            has_shoot[tank_id] = false;
        }
        else
            has_shoot[tank_id] = true;
    }
#ifdef DEBUG
    cout << "Shot state of " << tank_id << " is " << has_shoot[tank_id] << endl;
#endif
    return to_take;
}

int HeadQuarter::getEstimateScore(int x, int y, int dst_x, int dst_y)
{
    /* Can be further modified:
     TODO: come up with better strategy for path searching by modifying
     the estimation function here. 
    */
    return getManhattenDist(x, y, dst_x, dst_y);
}

void HeadQuarter::A_search(int tank_id, int dst_x, int dst_y)
{
    /*
    Implementation of A * search algorithm. Faster than BFS and can be adaptive.
    Let starting point be S, destinnation point be D
    for each nodes i in a graph G:
        f[i] = g[i] + h[i]
        g[i]: the REAL cost of getting to i from S
            can be calculated easily. g[i] = g[i-1] + cost(from i-1 to i)
        h[i]: the ESTIMATED cost of getting to D from i
            need sophisticated guess or estimate.
    the select path is stored in next_loc_{xy}
    */
    mySide = field->mySide;
    int x0 = field->tankX[mySide][tank_id];
    int y0 = field->tankY[mySide][tank_id];
    set<pair<int, int>> open_list, close_list;
    open_list.insert(make_pair(x0, y0));
    g_score[tank_id][y0][x0] = 0;
    h_score[tank_id][y0][x0] = getEstimateScore(x0, y0, dst_x, dst_y);
    pfather[tank_id][y0][x0] = -1;

    bool success = false;
    while (true)
    {

        auto min_loc = open_list.begin();
        int min_f = INF;
        for (auto it = open_list.begin(); it != open_list.end(); ++it)
        {
            int x = it->first, y = it->second;
            if (g_score[tank_id][y][x] + h_score[tank_id][y][x] < min_f)
            {
                min_loc = it;
                min_f = g_score[tank_id][y][x] + h_score[tank_id][y][x];
            }
        }
        close_list.insert(*min_loc);
        open_list.erase(*min_loc);
        int x = min_loc->first, y = min_loc->second;

        for (int i = 0; i < 4; ++i)
        {
            int _x = x + dx[i];
            int _y = y + dy[i];
            if (_x < 0 || _y < 0 || _x >= fieldWidth || _y >= fieldHeight)
                continue;

            if (close_list.find(make_pair(_x, _y)) != close_list.end() ||
                (field->gameField[_y][_x] & (Steel | Water)) != 0 ||
                (_y == baseY[mySide] && _x == baseX[mySide]))
            { //in close list or can't reach

                continue;
            }
            if (open_list.find(make_pair(_x, _y)) == open_list.end())
            {

                open_list.insert(make_pair(_x, _y));

                pfather[tank_id][_y][_x] = (i + 2) % 4;
                h_score[tank_id][_y][_x] = getEstimateScore(_x, _y, dst_x, dst_y);
                g_score[tank_id][_y][_x] = ((field->gameField[_y][_x] == Brick) ? 2 : 1) +
                                           g_score[tank_id][y][x];
            }
            else
            {

                if (g_score[tank_id][_y][_x] > ((field->gameField[_y][_x] == Brick) ? 2 : 1) + g_score[tank_id][y][x])
                {
                    g_score[tank_id][_y][_x] = ((field->gameField[_y][_x] == Brick) ? 2 : 1) + g_score[tank_id][y][x];
                    h_score[tank_id][_y][_x] = getEstimateScore(_x, _y, dst_x, dst_y);
                    pfather[tank_id][_y][_x] = (i + 2) % 4;
                }
            }
        }
        if (open_list.find(make_pair(dst_x, dst_y)) != open_list.end())
        {
            success = true;
            break;
        }
        else if (open_list.empty())
        {
            success = false;
            break;
        }
    }
    if (success)
    {
        int xx = dst_x, yy = dst_y;

        while (xx != x0 || yy != y0)
        {
            int tmp_x = xx, tmp_y = yy;
            next_loc_x[tank_id].push_front(xx);
            next_loc_y[tank_id].push_front(yy);
            xx = xx + dx[pfather[tank_id][tmp_y][tmp_x]];
            yy = yy + dy[pfather[tank_id][tmp_y][tmp_x]];
        }
#ifdef DEBUG
        cout << "A search succeeded." << endl;
        for (int i = 0; i < next_loc_x[tank_id].size(); ++i)
        {
            cout << next_loc_x[tank_id][i] << ',' << next_loc_y[tank_id][i] << endl;
        }
#endif
    }
#ifdef DEBUG
    else
    {
        cout << "A search failed." << endl;
    }
#endif
    memset(g_score, 0, sizeof(g_score));
    memset(h_score, 0, sizeof(h_score));
    memset(pfather, 0, sizeof(pfather));
}

Action HeadQuarter::Explore(int tank_id)
{
    // 10%的概率下，重新用A*算法搜路(把刚墙和水域视为不可入的)。
    // 若搜得路径的下一步是砖或者敌方基地，射击；若为空地，行走；其他情况，不动。
    if (first_move[tank_id] || (rand() % 100) > 90)
    {
        A_search(tank_id, baseX[otherSide], baseY[otherSide]);
        first_move[tank_id] = false;
    }

    int x0 = field->tankX[mySide][tank_id];
    int y0 = field->tankY[mySide][tank_id];
    int next_x = next_loc_x[tank_id].front();
    int next_y = next_loc_y[tank_id].front();

    int next_move = 0;
    for (int i = 0; i < 4; ++i)
    {
        if ((x0 + dx[i] == next_x) && (y0 + dy[i] == next_y))
        {
            next_move = i;
            break;
        }
    }

    if ((field->gameField[next_y][next_x] & (Brick | Base)) != 0)
    {                                   ///??? A star 把刚墙和水域视为不可入的了吗？
                                        ///??? 有可能打到自己的基地或清除自己基地旁边的保护墙吗？
        return (Action)(next_move + 4); // shoot
    }
    else if (field->gameField[next_y][next_x] == None)
    {
        next_loc_x[tank_id].pop_front();
        next_loc_y[tank_id].pop_front();
        return (Action)next_move;
    }
    else
    {
        return Stay;
    }
}

Action HeadQuarter::inShootRange(int tank_id, int e_tank_id)
{
    int x = field->tankX[mySide][tank_id];
    int y = field->tankY[mySide][tank_id];
    int ex = field->tankX[otherSide][e_tank_id];
    int ey = field->tankY[otherSide][e_tank_id];
#ifdef DEBUG
    cout << "My (x,y):" << '(' << x << ',' << y << ')' << endl;
    cout << "enemy (x,y):" << '(' << ex << ',' << ey << ')' << endl;
#endif
    if (x == ex && y == ey)
        return Stay;
    if (x == ex)
    {
        int i;
        Action to_take = (ey > y) ? DownShoot : UpShoot;
        for (i = y + ((ey > y) ? 1 : -1);
             (ey > y) ? (i <= ey) : (i >= ey);
             (ey > y) ? (i++) : (i--))
        {
            if ((field->gameField[i][x] & (Steel | Brick |
                                           ((mySide == Blue) ? (Blue0 | Blue1) : (Red0 | Red1)))) != 0)
                return RandActionExcept(tank_id, to_take);
            else if (i == ey)
                return to_take;
        }
    }
    if (y == ey)
    {
        int i;
        Action to_take = (ex > x) ? RightShoot : LeftShoot;
        for (i = x + ((ex > x) ? 1 : -1);
             (ex > x) ? (i <= ex) : (i >= ex);
             (ex > x) ? (i++) : (i--))
        {
            if ((field->gameField[y][i] & (Steel | Brick |
                                           ((mySide == Blue) ? (Blue0 | Blue1) : (Red0 | Red1)))) != 0)
                return RandActionExcept(tank_id, to_take);
            else if (i == ex)
                return to_take;
        }
    }
    return Stay;
}

Action HeadQuarter::Attack(int tank_id)
{
    Action move = inShootRange(tank_id, aim[tank_id][0]);
    if (move != Stay)
        return move;
    else
        return Stay;
}

Action HeadQuarter::Defend(int tank_id)
{
    A_search(tank_id, baseX[mySide], baseY[mySide]);

    int x0 = field->tankX[mySide][tank_id];
    int y0 = field->tankY[mySide][tank_id];
    int next_x = next_loc_x[tank_id].front();
    int next_y = next_loc_y[tank_id].front();

    int next_move = 0;
    for (int i = 0; i < 4; ++i)
    {
        if ((x0 + dx[i] == next_x) && (y0 + dy[i] == next_y))
        {
            next_move = i;
            break;
        }
    }

    if ((field->gameField[next_y][next_x] & (Brick)) != 0)
    {
        return (Action)(next_move + 4);
    }
    else if (field->gameField[next_y][next_x] == None)
    {
        next_loc_x[tank_id].pop_front();
        next_loc_y[tank_id].pop_front();
        return (Action)next_move;
    }
    else
        return Stay;
}

HeadQuarter *hq = new HeadQuarter;

} // namespace TankGame

int main()
{
#ifdef DEBUG
    freopen("debug.in", "r", stdin);
#endif
    srand((unsigned)time(nullptr));
    bool first_round = true;
    string data, globaldata;
    while (true)
    {
        if (first_round)
        {
            TankGame::ReadInput(cin, data, globaldata);
            TankGame::hq->mySide = TankGame::field->mySide;
            TankGame::hq->otherSide = (TankGame::field->mySide + 1) % 2;
            first_round = false;
#ifdef DEBUG
            cout << TankGame::field->mySide << endl;
            TankGame::field->DebugPrint();
            printf("Tank 0: %d, tank 1 : %d \n", TankGame::hq->cur_state[0], TankGame::hq->cur_state[1]);
#endif
        }
        else
        {
            TankGame::ReadInput_longlive(cin);
        }
        TankGame::SubmitAndDontExit(TankGame::hq->takeAction(0), TankGame::hq->takeAction(1));
        cout << flush;
    }
#ifdef DEBUG
    cout << TankGame::field->mySide << endl;
    TankGame::field->DebugPrint();
    TankGame::hq->A_search(1);
    TankGame::hq->A_search(0);
#endif
}