import pg from 'pg';
export declare class Database {
    private pool;
    constructor(connectionString: string);
    query(text: string, params?: any[]): Promise<import("pg").QueryResult<any>>;
    transaction<T>(callback: (client: pg.PoolClient) => Promise<T>): Promise<T>;
    close(): Promise<void>;
}
export declare function initDatabase(db: Database): Promise<void>;
