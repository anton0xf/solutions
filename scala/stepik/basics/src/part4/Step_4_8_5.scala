package part4

object Step_4_8_5 {
  def add(network: Map[String, Set[String]], location: String): Map[String, Set[String]] =
    network + (location -> Set())

  def connect(
               network: Map[String, Set[String]],
               locationA: String,
               locationB: String
             ): Map[String, Set[String]] = {
    network + (locationA -> (network(locationA) + locationB)) +
      (locationB -> (network(locationB) + locationA))
  }

  def disconnect(
                  network: Map[String, Set[String]],
                  locationA: String,
                  locationB: String
                ): Map[String, Set[String]] = {
    network + (locationA -> (network(locationA) - locationB)) +
      (locationB -> (network(locationB) - locationA))
  }

  def remove(network: Map[String, Set[String]], location: String): Map[String, Set[String]] = {
    (network - location).transform { (_, locs) => locs - location }
  }

  def flightCount(network: Map[String, Set[String]], location: String): Int = network(location).size

  def mostFlights(network: Map[String, Set[String]]): String = network.maxBy { kv => kv._2.size }._1

  def numLocationsWithNoFlights(network: Map[String, Set[String]]): Int = network.count { kv => kv._2.isEmpty }

  import scala.annotation.tailrec
  import scala.collection.immutable.Queue

  def isConnected(
                   network: Map[String, Set[String]],
                   locationA: String,
                   locationB: String
                 ): Boolean = {
    @tailrec
    def bfs(queue: Queue[String]): Boolean = {
      if (queue.isEmpty) false else {
        val (loc, q) = queue.dequeue
        (loc == locationB) || bfs(q.enqueue(network(loc)))
      }
    }

    bfs(Queue(locationA))
  }
}
